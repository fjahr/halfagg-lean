import Lean

/-!
# Two inventories of the compiled project

`Halfagg/Summary.lean` checks the axioms of the main results one by one. The
two commands here look at the whole project instead, and `Summary.lean` guards
their output as well.

* `#project_axioms` lists the axioms that the modules of the project declare
  and the axioms that the declarations of the project depend on. Axioms that
  no main result uses still show up here.
* `#surface c₁ c₂ …` lists the definitions that the statements of the given
  results depend on: the constants in the type of a theorem, and for a
  definition, a structure or an inductive type the constants in its type and
  its body, and so on. Proofs are not followed. The command follows
  definitions into taproot-lean, VCVio, agm-lean and the libraries that these
  are built on, and it stops at Lean's core library and at Mathlib. This is
  what a reader has to agree with to know what the results say. `REVIEW.md`
  lists the same definitions, and `scripts/check.sh` compares the two lists.
-/

open Lean Elab Command

namespace Halfagg.Audit

/-- The environment with the names of its modules, which are computed once. -/
structure Ctx where
  env : Environment
  mods : Array Name

def Ctx.of (env : Environment) : Ctx := ⟨env, env.header.moduleNames⟩

/-- The module that declares a constant. -/
def Ctx.moduleOf (x : Ctx) (c : Name) : Name :=
  match x.env.getModuleIdxFor? c with
  | some i => x.mods[i.toNat]!
  | none => x.env.header.mainModule

/-- Whether a constant is declared in a module of this project, or in the
module that is being compiled. -/
def Ctx.inProject (x : Ctx) (c : Name) : Bool :=
  match x.env.getModuleIdxFor? c with
  | some i => (`Halfagg).isPrefixOf x.mods[i.toNat]!
  | none => true

/-- The libraries whose definitions `#surface` does not list: Lean's core
library, Mathlib and what Mathlib is built on. -/
def baseLibraries : List Name :=
  [`Init, `Lean, `Std, `Mathlib, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets,
    `ImportGraph, `LeanSearchClient, `Cli]

/-- Whether `#surface` lists a constant: it is declared in this project or in
a library other than the base libraries. -/
def Ctx.listed (x : Ctx) (c : Name) : Bool :=
  match x.env.getModuleIdxFor? c with
  | some i => !baseLibraries.contains (x.mods[i.toNat]!).getRoot
  | none => true

/-- `#project_axioms`: the axioms declared in the project and the axioms that
its declarations depend on. -/
elab "#project_axioms" : command => do
  let x := Ctx.of (← getEnv)
  let consts := x.env.constants.fold (init := #[]) fun acc c info =>
    if x.inProject c then acc.push (c, info) else acc
  let declared := (consts.filterMap fun (c, info) =>
    match info with
    | .axiomInfo _ => some c
    | _ => none).qsort Name.lt
  let used ← liftCoreM do
    let mut used : NameSet := {}
    for (c, _) in consts do
      for a in ← collectAxioms c do
        used := used.insert a
    return used
  logInfo m!"axioms declared in the project: {declared}\naxioms that the project depends on: {used.toArray.qsort Name.lt}"

/-- The names of the auxiliary declarations that Lean generates next to a
definition or a type. -/
def auxSuffixes : List String :=
  ["below", "brecOn", "binductionOn", "casesOn", "recOn", "rec", "noConfusion",
    "noConfusionType", "ctorIdx", "toCtorIdx", "ctorElim", "ctorElimType", "sizeOf_spec",
    "injEq", "inj", "mk"]

/-- Whether a component of a name belongs to an auxiliary declaration. -/
def isAux : Name → Bool
  | .str _ s => s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" ||
      auxSuffixes.contains s
  | .num _ _ => true
  | .anonymous => false

/-- The declaration a reader sees for a constant: its type for a constructor,
a recursor or a projection, and the surrounding definition for an auxiliary
declaration such as a `match`. -/
def owner (env : Environment) (c : Name) : Name :=
  let c := (privateToUserName? c).getD c
  let c := match env.find? c with
    | some (.ctorInfo v) => v.induct
    | some (.recInfo v) => v.all.headD c
    | _ =>
      match env.getProjectionFnInfo? c with
      | some p => p.ctorName.getPrefix
      | none => c
  -- cut the name at its first auxiliary component
  let kept := c.components.takeWhile fun n => !isAux n
  kept.foldl (init := Name.anonymous) fun acc n =>
    match n with
    | .str _ s => .str acc s
    | .num _ k => .num acc k
    | .anonymous => acc

/-- Follow the listed constants in an expression. Theorems are not followed:
what a proof uses does not change what a statement says. -/
partial def visit (x : Ctx) (c : Name) : StateM NameSet Unit := do
  if (← get).contains c then return
  modify (·.insert c)
  let some info := x.env.find? c | return
  let follow (e : Expr) : StateM NameSet Unit :=
    e.getUsedConstants.forM fun d => do
      if x.listed d then
        match x.env.find? d with
        | some (.thmInfo _) => pure ()
        | _ => visit x d
  follow info.type
  match info with
  | .defnInfo v => follow v.value
  | .opaqueInfo v => follow v.value
  | .inductInfo v => v.ctors.forM (visit x)
  | _ => pure ()

/-- `#surface c₁ c₂ …`: the definitions behind the statements of the given
results, by module. -/
elab "#surface " ids:ident+ : command => do
  let x := Ctx.of (← getEnv)
  let env := x.env
  let mut seen : NameSet := {}
  for id in ids do
    let c := id.getId
    let some info := env.find? c | throwErrorAt id "unknown constant {c}"
    match info with
    | .thmInfo _ =>
      -- only the statement of a theorem
      let (_, s) := (info.type.getUsedConstants.forM fun d => do
        if x.listed d then
          match env.find? d with
          | some (.thmInfo _) => pure ()
          | _ => visit x d).run seen
      seen := s
    | _ =>
      let (_, s) := (visit x c).run seen
      seen := s
  let mut byModule : NameMap NameSet := {}
  for c in seen do
    let o := owner env c
    if env.contains o && x.listed o then
      let m := x.moduleOf o
      byModule := byModule.insert m (((byModule.find? m).getD {}).insert o)
  let lines := (byModule.toList.toArray.qsort fun a b => Name.lt a.1 b.1).map fun (m, s) =>
    s!"{m}: {", ".intercalate ((s.toArray.qsort Name.lt).toList.map toString)}"
  logInfo m!"{"\n".intercalate lines.toList}"

end Halfagg.Audit

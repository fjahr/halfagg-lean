/-! # Rows of the BIP458 test vector files -/

namespace Halfagg.Vectors

/-- A row of `test_vectors_aggregate.csv`. `expected = none` means
`Aggregate` must fail. -/
structure AggregateVector where
  index : Nat
  pubkeys : List String
  messages : List String
  signatures : List String
  expected : Option String
  comment : String

/-- A row of `test_vectors_incaggregate.csv`. `expected = none` means
`IncAggregate` must fail. -/
structure IncAggregateVector where
  index : Nat
  aggsig : String
  pmPubkeys : List String
  pmMessages : List String
  pubkeys : List String
  messages : List String
  signatures : List String
  expected : Option String
  comment : String

/-- A row of `test_vectors_verify.csv`. -/
structure VerifyVector where
  index : Nat
  aggsig : String
  pubkeys : List String
  messages : List String
  expected : Bool
  comment : String

end Halfagg.Vectors

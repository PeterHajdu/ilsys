module Simple

%default total

data LSys : a -> Type where
  MkLSys : List a -> (a -> List a) -> LSys a

iterate : Nat -> LSys a -> List a
iterate Z (MkLSys axiom _) = axiom
iterate n (MkLSys axiom rules) = go n axiom
  where
    go : Nat -> List a -> List a
    go Z word = word
    go (S n) word = let nextWord = word >>= rules
                     in go n nextWord


----------------
-- An example --
----------------

data Algae = A | B

Show Algae where
  show A = "A"
  show B = "B"

algaeRules : Algae -> List Algae
algaeRules A = [A, B]
algaeRules B = pure A

algaeExample : LSys Algae
algaeExample = MkLSys [A] algaeRules

main : IO ()
main = print $ Simple.iterate 10 algaeExample

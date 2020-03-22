module Stochastic

import Simple
import Effects
import Effect.Random

%default total

data Rule : Type -> Type where
  MkRule : a -> List (Int, List a) -> Rule a

data StochasticLSystem : Type -> Type where
  MkStoch : List a -> List (Rule a) -> StochasticLSystem a

makeGenerator : Eq a => List (Rule a) -> Eff (a -> List a) [RND]
makeGenerator _ = pure $ \x => [x]
--todo: finish

translate : Eq a => StochasticLSystem a -> Eff (LSys a) [RND]
translate (MkStoch axiom rules) = do
  generator <- makeGenerator rules
  pure $ MkLSys axiom generator


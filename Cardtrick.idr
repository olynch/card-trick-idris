module Cardgame

import Data.Fin
import Data.String
import Prelude.Algebra
import Effects
import Effect.Random
import Effect.StdIO
import Data.Vect
  
data Inserted : a -> Vect n a -> Vect (S n) a -> Type where
  InsHere : (x : a) -> (xs : Vect n a) -> Inserted x xs (x :: xs)
  InsThere : (y : a) -> Inserted x xs xs' -> Inserted x (y :: xs) (y :: xs')

data Perm : Vect n a -> Vect n a -> Type where
  Same : (xs : Vect n a) -> Perm xs xs
  Different : Perm xs ys -> Inserted y ys zs -> Perm (y :: xs) zs

insert : (x : a) -> Fin n -> (xs : Vect n a) -> (ys: Vect (S n) a ** Inserted x xs ys)
insert x FZ xs = (x :: xs ** InsHere _ _)
insert x (FS k) (y :: xs) with (insert x k xs)
  | (ys' ** prf) = (y :: ys' ** InsThere y prf)
    

shuffle : (xs : Vect n a) -> SimpleEff.Eff (ys : Vect n a ** Perm xs ys) [RND]
shuffle Nil = pure (Nil ** Same _)
shuffle [x] = pure ([x] ** Same _)
shuffle {n = S (S k)} (x :: xs) = do
  (ys ** prf_perm) <- shuffle xs
  rnd_idx <- rndFin k
  let (ys' ** prf_ins) = insert x rnd_idx ys
  pure (_ ** Different prf_perm prf_ins)

data AllUnique : Vect n a -> Type where
  UniqueNil : AllUnique Nil
  UniqueCons : (Elem x xs -> Void) -> AllUnique xs -> AllUnique (x :: xs)

parseCard : {xs : Vect p (Fin n)} -> String -> AllUnique xs -> Either String (ys : Vect (S p) (Fin n) ** AllUnique ys)
parseCard {n = n} {xs = xs} s prev = do
  let Just k = parseInteger s
    | Nothing => Left "You must input an integer. Use numerals (not words) and do not use a decimal point. Try again."
  let Just l = integerToFin (k - 1) n
    | Nothing => Left ("The integer must be between 1 and " <+> cast n)
  let No prf = isElem l xs
    | Yes _ => Left "You cannot have previously entered the integer"
  pure (_ ** UniqueCons prf prev)
    
getCards : (n: Nat) -> (k : Nat) -> SimpleEff.Eff (xs : Vect k (Fin n) ** AllUnique xs) [STDIO]
getCards n Z = pure (Nil ** UniqueNil)
getCards n (S l) = do
    v <- getCards n l
    loop v
  where
    loop : (xs : Vect k (Fin n) ** AllUnique xs) -> SimpleEff.Eff (ys : Vect (S k) (Fin n) ** AllUnique ys) [STDIO]
    loop (_ ** prf) = do
      putStrLn "\nEnter a number."
      s <- getStr
      case parseCard s prf of
        Left errorMsg => do
          putStrLn errorMsg
          loop (_ ** prf)
        Right newCards => pure newCards
      
-- main : IO ()
-- main = run $ do
--   (cards ** _) <- getCards 10 3
--   putStrLn $ 

-- Local Variables:
-- idris-load-packages: ("effects" "base")
-- End:

module Imp1 where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

data Bool =
   True
 | False

bool_rect :: a1 -> a1 -> Bool -> a1
bool_rect f f0 b =
  case b of {
   True -> f;
   False -> f0}

bool_rec :: a1 -> a1 -> Bool -> a1
bool_rec =
  bool_rect

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

negb :: Bool -> Bool
negb b =
  case b of {
   True -> False;
   False -> True}

data Nat =
   O
 | S Nat

data Option a =
   Some a
 | None

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

mul :: Nat -> Nat -> Nat
mul n m =
  case n of {
   O -> O;
   S p -> add m (mul p m)}

sub :: Nat -> Nat -> Nat
sub n m =
  case n of {
   O -> n;
   S k -> case m of {
           O -> n;
           S l -> sub k l}}

bool_dec :: Bool -> Bool -> Sumbool
bool_dec b1 b2 =
  bool_rec (\x -> case x of {
                   True -> Left;
                   False -> Right}) (\x -> case x of {
                                            True -> Right;
                                            False -> Left}) b1 b2

eqb :: Nat -> Nat -> Bool
eqb n m =
  case n of {
   O -> case m of {
         O -> True;
         S _ -> False};
   S n' -> case m of {
            O -> False;
            S m' -> eqb n' m'}}

leb :: Nat -> Nat -> Bool
leb n m =
  case n of {
   O -> True;
   S n' -> case m of {
            O -> False;
            S m' -> leb n' m'}}

data Ascii0 =
   Ascii Bool Bool Bool Bool Bool Bool Bool Bool

ascii_rect :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> a1) -> Ascii0 -> a1
ascii_rect f a =
  case a of {
   Ascii b b0 b1 b2 b3 b4 b5 b6 -> f b b0 b1 b2 b3 b4 b5 b6}

ascii_rec :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> a1) -> Ascii0 -> a1
ascii_rec =
  ascii_rect

ascii_dec :: Ascii0 -> Ascii0 -> Sumbool
ascii_dec a b =
  ascii_rec (\b0 b1 b2 b3 b4 b5 b6 b7 x ->
    case x of {
     Ascii b8 b9 b10 b11 b12 b13 b14 b15 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> sumbool_rec (\_ -> Left) (\_ -> Right) (bool_dec b7 b15)) (\_ -> Right)
                    (bool_dec b6 b14)) (\_ -> Right) (bool_dec b5 b13)) (\_ -> Right) (bool_dec b4 b12)) (\_ ->
              Right) (bool_dec b3 b11)) (\_ -> Right) (bool_dec b2 b10)) (\_ -> Right) (bool_dec b1 b9)) (\_ ->
        Right) (bool_dec b0 b8)}) a b

data String =
   EmptyString
 | String0 Ascii0 String

string_rect :: a1 -> (Ascii0 -> String -> a1 -> a1) -> String -> a1
string_rect f f0 s =
  case s of {
   EmptyString -> f;
   String0 a s0 -> f0 a s0 (string_rect f f0 s0)}

string_rec :: a1 -> (Ascii0 -> String -> a1 -> a1) -> String -> a1
string_rec =
  string_rect

string_dec :: String -> String -> Sumbool
string_dec s1 s2 =
  string_rec (\x -> case x of {
                     EmptyString -> Left;
                     String0 _ _ -> Right}) (\a _ h x ->
    case x of {
     EmptyString -> Right;
     String0 a0 s ->
      sumbool_rec (\_ -> sumbool_rec (\_ -> Left) (\_ -> Right) (h s)) (\_ -> Right) (ascii_dec a a0)}) s1 s2

eqb_string :: String -> String -> Bool
eqb_string x y =
  case string_dec x y of {
   Left -> True;
   Right -> False}

type Total_map a = String -> a

t_update :: (Total_map a1) -> String -> a1 -> String -> a1
t_update m x v x' =
  case eqb_string x x' of {
   True -> v;
   False -> m x'}

type State = Total_map Nat

data Aexp =
   ANum Nat
 | AId String
 | APlus Aexp Aexp
 | AMinus Aexp Aexp
 | AMult Aexp Aexp

data Bexp =
   BTrue
 | BFalse
 | BEq Aexp Aexp
 | BLe Aexp Aexp
 | BNot Bexp
 | BAnd Bexp Bexp

aeval :: State -> Aexp -> Nat
aeval st a =
  case a of {
   ANum n -> n;
   AId x -> st x;
   APlus a1 a2 -> add (aeval st a1) (aeval st a2);
   AMinus a1 a2 -> sub (aeval st a1) (aeval st a2);
   AMult a1 a2 -> mul (aeval st a1) (aeval st a2)}

beval :: State -> Bexp -> Bool
beval st b =
  case b of {
   BTrue -> True;
   BFalse -> False;
   BEq a1 a2 -> eqb (aeval st a1) (aeval st a2);
   BLe a1 a2 -> leb (aeval st a1) (aeval st a2);
   BNot b1 -> negb (beval st b1);
   BAnd b1 b2 -> andb (beval st b1) (beval st b2)}

data Com =
   CSkip
 | CAss String Aexp
 | CSeq Com Com
 | CIf Bexp Com Com
 | CWhile Bexp Com

ceval_step :: State -> Com -> Nat -> Option State
ceval_step st c i =
  case i of {
   O -> None;
   S i' ->
    case c of {
     CSkip -> Some st;
     CAss l a1 -> Some (t_update st l (aeval st a1));
     CSeq c1 c2 -> case ceval_step st c1 i' of {
                    Some st' -> ceval_step st' c2 i';
                    None -> None};
     CIf b c1 c2 -> case beval st b of {
                     True -> ceval_step st c1 i';
                     False -> ceval_step st c2 i'};
     CWhile b1 c1 ->
      case beval st b1 of {
       True -> case ceval_step st c1 i' of {
                Some st' -> ceval_step st' c i';
                None -> None};
       False -> Some st}}}


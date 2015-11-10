module Problem3 where

import qualified Prelude

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

data Bool =
   True
 | False

data Nat =
   O
 | S Nat

data Stack t =
   Empty
 | Add t (Stack t)

stack_rect :: a2 -> (a1 -> (Stack a1) -> a2 -> a2) -> (Stack a1) -> a2
stack_rect f f0 s =
  case s of {
   Empty -> f;
   Add y s0 -> f0 y s0 (stack_rect f f0 s0)}

stack_rec :: a2 -> (a1 -> (Stack a1) -> a2 -> a2) -> (Stack a1) -> a2
stack_rec =
  stack_rect

push :: a1 -> (Stack a1) -> Stack a1
push t st =
  Add t st

pop :: (Stack a1) -> Stack a1
pop s =
  case s of {
   Empty -> false_rect;
   Add e s' -> s'}

top :: (Stack a1) -> a1
top s =
  case s of {
   Empty -> false_rect;
   Add t s0 -> t}

s1 :: Stack Nat
s1 =
  Add (S (S (S O))) Empty

isEmpty :: (Stack a1) -> Bool
isEmpty s =
  case s of {
   Empty -> True;
   Add t s0 -> False}

size :: (Stack a1) -> Nat
size s =
  case s of {
   Empty -> O;
   Add t ns' -> S (size ns')}


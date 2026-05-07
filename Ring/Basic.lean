import Mathlib.Data.Set.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
-- import Mathlib.Algebra.Ring.Basic

namespace CommRing


class Ring α extends AddCommGroup α where
  one: α
  mul: α → α → α
  mul_one (a: α): mul a one = a
  mul_comm (a b: α): mul a b = mul b a
  mul_assoc (a b c: α): mul (mul a b) c = mul a (mul b c)
  left_distrib (a b c : α) : mul a (b + c) = mul a b + mul a c
  right_distrib (a b c : α) : mul (a + b) c = mul a c + mul b c


instance [Ring α]: One α where
  one := Ring.one

instance [Ring α]: Mul α where
  mul := Ring.mul

class Hom α β [Ring α] [Ring β] extends AddMonoidHom α β   where
  map_mul (a b: α): toFun (a * b) = toFun a * toFun b
  map_one: toFun 1 = 1

class Ideal α [Ring α] extends AddSubgroup α where
  left_mul_mem (a b: α): a ∈ carrier → a * b ∈ carrier
  right_mul_mem (a b: α): b ∈ carrier → a * b ∈ carrier

def zero_divisor [Ring α] (x: α): Prop := ∃ (y: α), x * y = 0

def unit [Ring α] (x: α): Prop := ∃ (y: α), x * y = 1























end CommRing

def hello := "world"

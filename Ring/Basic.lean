import Mathlib.Data.Set.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
-- import Mathlib.Algebra.Ring.Basic

namespace Ring


class CommRing α extends AddCommGroup α where
  one: α
  mul: α → α → α
  mul_one (a: α): mul a one = a
  mul_comm (a b: α): mul a b = mul b a
  mul_assoc (a b c: α): mul (mul a b) c = mul a (mul b c)
  left_distrib (a b c : α) : mul a (b + c) = mul a b + mul a c
  right_distrib (a b c : α) : mul (a + b) c = mul a c + mul b c


instance [CommRing α]: One α where
  one := CommRing.one

instance [CommRing α]: Mul α where
  mul := CommRing.mul

class CommRingHom α β [CommRing α] [CommRing β] where
  map_func: α → β
  map_add (a b: α): map_func (a + b) = map_func a + map_func b
  map_mul (a b: α): map_func (a * b) = map_func a * map_func b
  map_zero: map_func 0 = 0
  map_one: map_func 1 = 1

class Ideal α [CommRing α] extends AddSubgroup α where
  mul_closed (a b: α): a ∈ carrier → b ∈ carrier → a * b ∈ carrier



def zero_divisor [CommRing α] (x: α): Prop := ∃ (y: α), x * y = 0

def unit [CommRing α] (x: α): Prop := ∃ (y: α), x * y = 1























end Ring

def hello := "world"

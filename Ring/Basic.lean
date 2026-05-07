import LLMlean

import Mathlib.Data.Set.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Subgroup.Ker
-- import Mathlib.Algebra.Ring.Basic

import Mathlib.Data.Set.Operations

namespace CommRing


class Ring (α : Type*) extends AddCommGroup α, Mul α, One α where
  mul_one {a : α} : a * 1 = a
  mul_comm {a b : α} : a * b = b * a
  mul_assoc {a b c : α} : (a * b) * c = a * (b * c)
  left_distrib {a b c : α} : a * (b + c) = a * b + a * c

def Ring.right_distrib [Ring α] {a b c : α} : (a + b) * c = a * c + b * c := by
  conv_lhs =>
    rw [Ring.mul_comm]
    rw [Ring.left_distrib]
    rw [@Ring.mul_comm α _ c a]
    rw [@Ring.mul_comm α _ c b]



class Hom α β [Ring α] [Ring β] extends AddMonoidHom α β   where
  map_mul {a b: α}: toFun (a * b) = toFun a * toFun b
  map_one: toFun 1 = 1

structure Ideal α [Ring α] extends AddSubgroup α where
  left_mul_mem {a b: α}: a ∈ carrier → a * b ∈ carrier

def Ideal.right_mul_mem [Ring α] {i: Ideal α} {a b: α}: b ∈ i.carrier → a * b ∈ i.carrier := by
  intro hb
  rw [Ring.mul_comm]
  exact (i.left_mul_mem hb)

theorem zero_mul [Ring α]: ∀ (a: α), 0 * a = 0 := by
  intro a
  have h: 0 * a + 0 * a = 0 * a + 0 := by
    conv_rhs =>
      rw [add_zero (0 * a)]
      rw [show (0: α) = 0 + 0 by simp]

      rw [Ring.right_distrib]
  exact add_left_cancel h

theorem mul_zero [Ring α]: ∀ (a: α), a * 0 = 0 := by
  intro a
  conv_lhs =>
    rw [Ring.mul_comm]
    rw [zero_mul]

def zero_divisor [Ring α] (x: α): Prop := ∃ (y: α), x * y = 0

def unit [Ring α] (x: α): Prop := ∃ (y: α), x * y = 1

def kernel [Ring α] [Ring β] (f: Hom α β): Set α := {x: α | f.toFun x = 0}

def kernel_is_ideal [Ring α] [Ring β] (f: Hom α β): Ideal α := by
  let k: Set α := kernel f
  let add_mem' {a b : α}: a ∈ k → b ∈ k → (a + b) ∈ k := by
    intro ha hb

    change a ∈ {x: α | f.toFun x = 0} at ha
    simp [Set.mem_setOf_eq] at ha

    change b ∈ {x: α | f.toFun x = 0} at hb
    simp [Set.mem_setOf_eq] at hb

    change (a + b) ∈ {x: α | f.toFun x = 0}
    simp [Set.mem_setOf_eq]
    rw [ha, hb]
    rw [AddMonoid.add_zero]

  let zero_mem': (0: α) ∈ k := by
    change 0 ∈ {x: α | f.toFun x = 0}
    simp only [Set.mem_setOf_eq]
    simp [AddMonoidHom.map_zero f.toAddMonoidHom]

  let neg_mem' {a: α}: (a ∈ k) → (-a ∈ k) := by
    intro ha
    change a ∈ {x: α | f.toFun x = 0} at ha
    change -a ∈ {x: α | f.toFun x = 0}
    simp [Set.mem_setOf_eq] at ha
    simp [Set.mem_setOf_eq]
    exact ha


  let left_mul_mem {a b: α}: a ∈ k → a * b ∈ k := by
    intro ha
    change a ∈ {x: α | f.toFun x = 0} at ha
    change a * b ∈ {x: α | f.toFun x = 0}
    simp [Set.mem_setOf_eq] at ha
    simp [Set.mem_setOf_eq]

    show f.toFun (a * b) = 0
    rw [f.map_mul]
    simp [ha]
    rw [zero_mul]




  exact {
    carrier   := k,
    add_mem'  := add_mem',
    zero_mem' := zero_mem',
    neg_mem'  := neg_mem',
    left_mul_mem := left_mul_mem,
  }


end CommRing

def hello := "world"

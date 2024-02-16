import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import MIL.Common

open Nat

def f (x: Nat) :=
  x + 3

#check f

#check 2 + 2 = 4

#check 2 + 2 = 5

def FermatLastTheorem :=
  ∀ x y z n: ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

def FermatLastTheoremCompact :=
  ∀ x y z n : ℕ, n>2∧x*y*z≠0→x^n+y^n≠z^n

theorem equiv : FermatLastTheorem ↔ FermatLastTheoremCompact :=
  sorry

theorem hard : FermatLastTheoremCompact :=
  sorry

#check hard

example : ∀ m n:ℕ,Even n → Even (m*n) :=
  fun m n ⟨k, (hk: n=k+k )⟩ ↦
  have hmn : m*n=m*k+m*k := by rw [hk, mul_add]
  show ∃l,m*n=l+l from ⟨_, hmn⟩

-- This example fails; rw must be followed by equality first
example : ∀ m n:ℕ,Even n → Even (m*n) :=
  fun m n ⟨k, (hk: n=k+k )⟩ ↦
  have hmn : m*n=m*k+m*k := by rw [mul_add, hk]
  show ∃l,m*n=l+l from ⟨_, hmn⟩

-- Perfect! three steps of function application
example : ∀ m n:ℕ,Even n → Even (m*n) :=
  fun m n ⟨k, (hk: n=k+k)⟩ ↦
  have x := mul_add m k k
  have y : m*n=m*k+m*k := by rw [hk, x]
  have z : Even (m*n) := ⟨ m*k, y ⟩
  z

example : ∀ m n:ℕ,Even n→ Even (m*n) := by
  rintro m n ⟨k,hk⟩
  use m*k
  rw [hk]
  ring

example : ∀ m n:ℕ,Even n→ Even (m*n) := by
  rintro m n ⟨k,hk⟩; use m*k; rw [hk]; ring

example : ∀ m n:ℕ,Even n→ Even (m*n) := by
  intros; simp [*, parity_simps]


-- Only * seems to be necessary
example : ∀ m n:ℕ,Even n→ Even (m*n) := by
  intros; simp [*]

-- My own proof! Use apply to create functions
example : ∀ m n:ℕ,Even n→ Even (m*n) := by
  rintro m n ⟨k,hk⟩; simp [parity_simps];
  apply Or.inr ⟨k,hk⟩;

-- Ring proves a lot of things
example: ∀ a b: ℕ,a+b=b+a := by ring
-- but you need to use intros first
example: ∀ a b: ℕ,a+b=b+a := by intros; ring
example: ∀ a b: ℕ,a*b=b*a := by intros; ring
example: ∀ a b c: ℕ,a*(b+c)=b*a+a*c := by intros; ring
example: ∀ a b c: ℝ,a*(b+c)=b*a+a*c := by intros; ring
example: ∀ a b c: ℂ,a*(b+c)=b*a+a*c := by intros; ring

-- Manual
example (a b c: ℝ) : a*b*c=b*(a*c) := by
  rw [mul_comm a b];
  rw [mul_assoc b a c]

section
variable (a b c : ℝ)
#check mul_assoc b a c
end

#check fun (a b c : ℝ) ↦ mul_assoc b a c

#check fun (a b c : ℝ) ↦  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b

section
variable (a b c : ℝ)
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry

end

-- Ring theory
section
variable (R : Type*) [Ring R]
#check (add_assoc : ∀ a b c: R, a+b+c=a+(b+c))
#check (add_assoc : ∀ a b c: R, a+b+c=a+(c+b))

-- This example does not work because ring does not commute
example : ∀ a b
c:R,a+b+c=a+(c+b) := by
  intros; ring
-- needs ring_nf
example : ∀ a b
c:R,a+b+c=a+(b+c) := by
  intros; ring!

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
end

section
variable (R : Type*) [CommRing R]

#check (add_assoc : ∀ a b c: R, a+b+c=a+(b+c))
#check (add_assoc : ∀ a b c: R, a+b+c=a+(c+b))

-- this works
example : ∀ a b
c:R,a+b+c=a+(c+b) := by
  intros; ring

variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, add_left_neg]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable (R : Type*) [CommRing R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, add_left_neg, zero_add]

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_right_neg, add_comm, zero_add]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  -- order is important; keep parentheses!
  -- this doesn't work:
  --have g: -a+a+b=-a+a+c := by
  --  rw [h]
  have g: -a+(a+b)=-a+(a+c) := by rw [h]
  rw [neg_add_cancel_left, add_comm] at g
  nth_rw 2 [add_comm] at g
  rw [add_neg_cancel_right] at g
  use g

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  have g: a+b+(-b)=c+b+(-b) := by rw [h]
  have g1: a+b+(-b)=a := by rw [add_neg_cancel_right]
  have g2: c+b+(-b)=c := by rw [add_neg_cancel_right]
  rw [← g1, ← g2, g]

example (a b: R) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]
end MyRing

namespace MyRing2
variable (R : Type*) [CommRing R]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h: 0 * a + 0 * a = 0 * a + 0 := by
    rw [←add_mul, add_zero, add_zero]
  -- rw [add_left_cancel h]
  exact add_left_cancel h

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_comm, add_left_neg]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two, add_mul, one_mul]

end MyRing2

namespace MyGroup3
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (add_left_neg : ∀ a : A, -a + a = 0)

variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  have h8: (a⁻¹)⁻¹*a⁻¹=1 := by
    rw [mul_left_inv]
  have h9: (a⁻¹)⁻¹*a⁻¹*a*a⁻¹=1 := by
    nth_rw 2 [mul_assoc]
    rw [mul_left_inv, mul_assoc, one_mul, mul_left_inv]
  rw [←h9, h8, one_mul]

theorem mul_right_inv2 (a : G) : a * a⁻¹ = 1 := by
  have h9: (a⁻¹)⁻¹*a⁻¹*a*a⁻¹=1 := by
    nth_rw 2 [mul_assoc]
    rw [mul_left_inv, mul_assoc, one_mul, mul_left_inv]
  rw [←h9, mul_left_inv, one_mul]


theorem mul_right_inv3 (a : G) : a * a⁻¹ = 1 := by
  rw [
    ← one_mul (a*a⁻¹),
    ← mul_left_inv a⁻¹,
    mul_assoc,
    ←mul_assoc a⁻¹,
    mul_left_inv,
    one_mul
  ]

theorem mul_one (a : G) : a * 1 = a := by
  rw [
    ←mul_left_inv a,
    ←mul_assoc,
    mul_right_inv,
    one_mul
  ]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [
    ← one_mul (a*b)⁻¹,
    ← mul_left_inv b,
    ← mul_one b⁻¹,
    mul_assoc b⁻¹,
    ← mul_left_inv a,
    mul_assoc,
    mul_assoc a⁻¹,
    mul_assoc,
    mul_right_inv (a*b),
    mul_one,
    ← mul_assoc,
    mul_assoc,
    mul_right_inv,
    mul_one
  ]

theorem mul_inv_rev2 (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=  by simp

end MyGroup3

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Opposites
import Mathlib.Tactic

/--
A more computable version of bijective.
-/
structure HasInverse (f : α → β) where
  inv : β → α
  right : Function.LeftInverse f inv
  left : Function.LeftInverse inv f

/--
A quasigroup is a set with a binary operation such that left and right mulision are always possible.
-/
class QuasiGroup (G : Type*) extends Mul G where
  right_quotient (a : G) : HasInverse (a * ·)
  left_quotient (a : G) : HasInverse (· * a)

/--
A loop is a set with a binary operation that has a two-sided identity element,
and for which left and right mulision are always possible.
-/
class abbrev Loop (G : Type*) := MulOneClass G, QuasiGroup G

@[simps] class LeftBolLoop (G : Type*) extends Loop G, Inv G where
  -- __ := inferInstanceAs $ Inv G
  left_bol (x y z : G) : x * (y * (x * z)) = ((x * y) * x) * z
  inv a := (right_quotient a).inv 1
  biinv (a : G) : (a⁻¹ * a) = 1 ∧ (a * a⁻¹) = 1 := by rfl

theorem inv_behaves [l : LeftBolLoop G] (a : G) : (a⁻¹ * a) = 1 ∧ (a * a⁻¹) = 1 := by
  exact l.biinv a
/--
A Moufang loop is a loop that is both left and right Bol loop.
-/
class MoufangLoop (G : Type*) extends Loop G where
  left_bol (x y z : G) : x * (y * (x * z)) = ((x * y) * x) * z
  right_bol (x y z : G) : ((z * x) * y) * z = z * (x * (y * x))
  moufang (x y z : G) : (x * y) * (z * x) = x * (y * z) * x := by
    rfl

class Moufang

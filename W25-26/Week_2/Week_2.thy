theory Week_2
imports Main
begin

lemma "(x::nat) + y = y + x"
proof(induction x)
  case 0
  have 1: "0 + y = y"
    using Groups.comm_monoid_add_class.add_0[where ?a = y]
    .

  have 2: "y + 0 = y"
    using Groups.monoid_add_class.add_0_right
    .

  show ?case
    apply(subst 1)
    apply(subst 2)
    ..

next
  case (Suc x)
  have 1: "(Suc x) + y = Suc (x + y)"
    using Nat.plus_nat.add_Suc
    .

  have 2: "y + Suc x = Suc (y + x)"
    using Nat.add_Suc_right
    .

  show ?case
    apply(subst 1)
    apply(subst 2)
    apply(subst Suc.IH)
    ..

qed

     
end

theory Distrib_Eg
  imports Complex_Main
begin

thm refl

(*Show them how to search for a theorem*)

thm semiring_class.distrib_left

thm mult.commute

thm add.assoc

(*

  talk about the types of the variables and the overloading of * and +
  type inference deduces the other types by setting one variable

*)

lemma "((x::nat) + y) * (a + b) = a * x + a * y + b * x + b * y"
proof-

  (*Note that we do not need to annotate the constants here as their types come from the thm
    statement*) 
  have 1: "(x + y) * (a + b) = (x + y) * (a + b)"
    (*First use apply then by*)
    (*Discuss that rule does forward reasoning. Here it finishes as refl has no pending assumptions*)
    apply (rule refl)
    .

  from 1 have 2: "(x + y) * (a + b) = (x + y) * a + (x + y) * b"
    (*show them them the proof state, with the chained fact*)
    apply(subst (asm) (2) semiring_class.distrib_left)
    .
  (*hence instead of from 2*)
  hence 3: "(x + y) * (a + b) = a * (x + y) + (x + y) * b"
   by(subst (asm) (2) mult.commute)
  hence 4: "(x + y) * (a + b) = a * (x + y) + b * (x + y)"
    apply(subst (asm) (3) mult.commute)
    .
  hence 5: "(x + y) * (a + b) = a * x + a * y + b * (x + y)"
    apply(subst (asm) (2) semiring_class.distrib_left)
    .
  hence 6: "(x + y) * (a + b) = a * x + a * y + (b * x + b * y)"
    by(subst (asm) (2) semiring_class.distrib_left)
  thus ?thesis
    (*Note that symmetric here creates the flipped equation*)
    by(subst (asm) add.assoc[symmetric])
qed

(*Now let's try the same proof with equational reasoning*)

lemma "((x::nat) + y) * (a + b) = a * x + a * y + b * x + b * y"
proof-
  have "(x + y) * (a + b) = (x + y) * a + (x + y) * b"
    (*show them them the proof state, now we have no chained fact, and accordingly the subst
      directly changes the goal*)
    apply(subst semiring_class.distrib_left)
    (*for goals of the form A |- x = x, close them with ..*)
    ..
  (*hence instead of from 2*)
  also have "... = a * (x + y) + (x + y) * b"
    apply (subst (1)  mult.commute)
    ..
  also have "... = a * (x + y) + b * (x + y)"
    apply(subst (2) mult.commute)
    ..
  also have "... = a * x + a * y + b * (x + y)"
    apply(subst (1) semiring_class.distrib_left)
    ..
  also have "... = a * x + a * y + (b * x + b * y)"
    apply (subst (1) semiring_class.distrib_left)
    ..
  also have "... = a * x + a * y + b * x + b * y"
    apply(subst add.assoc[symmetric])
    ..
  finally show ?thesis
    .
qed

end


theory LGT
  imports Main
begin

fun fold::"('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
"fold f [] acc = acc"
| "fold f (x # xs) acc = fold f xs (f x acc)"

fun list_sum:: "nat list \<Rightarrow> nat" where
"list_sum [] = 0"
| "list_sum (x # xs) = x + list_sum xs"

fun list_sum':: "nat list \<Rightarrow> nat" where
  "list_sum' xs = fold (+) xs 0"

lemma "\<And>acc. acc + list_sum xs = fold (+) xs acc"
proof(induction xs)
  case Nil
  thm list_sum.simps(1)
  thm fold.simps(1)
  show ?case
    apply(subst list_sum.simps(1))
    apply(subst fold.simps(1))
    apply(subst add_0_right)
    ..
next
  case (Cons a xs)

  show ?case
    apply(subst list_sum.simps(2))
    apply(subst fold.simps(2))
    apply(subst add.assoc[symmetric])
    apply(subst add.commute)
    apply(subst Cons.IH)
    ..  
qed

lemma "\<And>acc. acc + list_sum xs = fold (+) xs acc"
proof(induction xs)
  case Nil
  have "acc + list_sum [] = acc + 0"
    apply(subst list_sum.simps(1))
    ..
  also have "... = acc"
    apply(subst add_0_right)
    ..
  also have "... = fold (+) [] acc"
    apply(subst fold.simps(1))
    ..
  finally show ?case
    .
next
  case (Cons a xs)

  have "acc + list_sum (a#xs) = acc + (a + list_sum xs)"
    apply(subst list_sum.simps(2))
    ..
  also have "... = acc + a + list_sum xs"
    apply(subst add.assoc[symmetric])
    ..
  also have "... = a + acc + list_sum xs"
    apply(subst add.commute)
    ..
  also have "... = fold (+) xs (a+acc)"
    apply(subst Cons.IH)
    ..
  also have "... = fold (+) (a#xs) acc"
    apply(subst fold.simps(2)[symmetric])
    ..

  finally show ?case
    .
qed

thm rev.simps

fun rev_tr_aux::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_tr_aux []     acc = acc"
| "rev_tr_aux (x#xs) acc = rev_tr_aux xs (x # acc)" 

value "rev_tr_aux [1::nat,2,3] []"


fun rev_tr::"'a list \<Rightarrow> 'a list" where
  "rev_tr xs = rev_tr_aux xs []"


lemma "rev xs @ (a # ys) = rev (a # xs) @ ys"
  by auto


lemma rev_tr_aux_eq_rev: "\<And>acc. rev_tr_aux xs acc = (rev xs) @ acc"
proof(induction xs)
  case Nil
  then show ?case
    by auto
next
  case (Cons a xs)
  have "rev_tr_aux (a # xs) acc = rev_tr_aux xs (a # acc)"
    apply(subst rev_tr_aux.simps)
    ..
  also have "... = rev xs @ (a # acc)"
    apply(subst Cons.IH)
    ..
  also have "... = (rev xs) @ ([a] @ acc)"
    apply(subst append.simps)
    apply(subst append.simps)
    ..
  also have "... = (rev xs @ [a]) @ acc "
    apply(subst append.assoc)
    ..
  also have "... = rev (a # xs) @ acc "
    apply(subst rev.simps)
    ..
  finally have "rev_tr_aux (a # xs) acc = rev (a#xs) @ acc"
    .
  then show ?case
    .
qed

lemma "rev_tr xs = rev xs"
  by (auto simp: rev_tr_aux_eq_rev)


  


end
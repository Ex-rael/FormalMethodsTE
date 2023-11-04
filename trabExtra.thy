theory t2
  imports Main
begin

primrec mult :: "nat ⇒ nat ⇒ nat" where
  "mult x 0 = 0" |
  "mult x (Suc y) = x + mult x y"

lemma l1: "∀x. mult x y = x * y"
proof (induction y)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof
    fix x
    from `mult x n = x * n` have "x + mult x n = x + x * n" by simp
    also have "... = x * Suc n" by (simp add: mult_succ_right)
    finally show "mult x (Suc n) = x * Suc n" by (simp add: mult.simps)
  qed
qed

lemma l2: "∀x. mult x y = mult y x"
proof (induction y)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof
    fix x
    from `mult x n = mult n x` have "mult x (Suc n) = x + mult x n" by (simp add: mult.simps)
    also have "... = x + mult n x" using `mult x n = mult n x` by simp
    also have "... = mult (Suc n) x" by (simp add: mult.simps)
    finally show "mult x (Suc n) = mult (Suc n) x" by simp
  qed
qed

lemma l3: "∀x y. mult x (mult y z) = mult (mult x y) z"
proof (induction z)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof
    fix x y
    from `mult x (mult y n) = mult (mult x y) n` have "mult x (mult y (Suc n)) = mult x (y + mult y n)" by (simp add: mult.simps)
    also have "... = mult x y + mult x (mult y n)" by (simp add: mult.simps)
    also have "... = mult x y + mult (mult x y) n" using `mult x (mult y n) = mult (mult x y) n` by simp
    also have "... = x * y + mult (mult x y) n" by (simp add: l1)
    also have "... = x * y + x * mult y n" by (simp add: l1)
    also have "... = x * (y + mult y n)" by (simp add: left_distrib)
    also have "... = mult (mult x y) (Suc n)" by (simp add: mult.simps)
    finally show "mult x (mult y (Suc n)) = mult (mult x y) (Suc n)" by simp
  qed
qed

end

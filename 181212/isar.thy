theory isar
  imports Main
begin

thm surj_def

lemma "\<not>surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by (simp add:surj_def)
  thus "False" by blast
qed

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof -
  have "\<exists>a. {x. x \<notin> f x } = f a" using s
    by (auto simp: surj_def)
  thus "False" by blast
qed

lemma "\<not>surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by (auto simp: surj_def)
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast
  thus "False" by blast
qed

lemma fixes a b :: int assumes "b dvd (a + b)" shows "b dvd a"
proof - {
  fix k assume k: "a + b = b * k"
  have "\<exists>k'. a = b * k'"
  proof
    show "a = b * (k - 1)" using k by (simp add:algebra_simps)
  qed }
  then show ?thesis using assms by (auto simp add: dvd_def)
qed

(* exercise 5.1 *)

lemma
  assumes T: "\<forall>x y. T x y \<or> T y x"
  and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall>x y. T x y \<longrightarrow> A x y"
  and "A x y"
  shows "T x y"
proof (rule ccontr)
  assume "\<not> T x y"
  from this and T have "T y x" by blast
  from this and TA have "A y x" by blast
  from this and `A x y` and A have "x = y" by blast
  from this and `\<not>T x y` and `T y x` show "False" by blast
qed

(* exercise 5.2 *)

lemma
  "(\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs) \<or>
   (\<exists>ys zs. xs = ys @ zs \<or> length ys = length zs + 1)"
proof cases
  assume " 2 dvd (length xs)"
  then obtain k where xsk: "(length xs) = 2 * k" by (auto simp add: dvd_def)
  obtain ys where ys: "ys = take k xs" by auto
  obtain zs where zzs: "zs = drop k xs" by auto
  have "length ys = k" using ys and xsk by auto
  then have "xs = ys @ zs" using ys and zzs by (metis append_eq_conv_conj)
  moreover have "length ys = length zs" using zzs and ys and xsk by auto
  ultimately show ?thesis by auto
next
  assume "\<not> 2 dvd (length xs)"
  hence "\<exists> k. length xs = 2 * k + 1" by arith
  then obtain k where xsk: "length xs = 2 * k + 1" by blast
  obtain ys where yys: "ys = take (Suc k) xs" by auto
  obtain zs where zzs: "zs = drop (Suc k) xs" by auto
  have "length ys = Suc k" using yys and xsk by auto
  hence "xs = ys @ zs" using yys and zzs by (metis append_eq_conv_conj)
  moreover have "length ys = length zs + 1" using zzs and yys and xsk by auto
  ultimately show ?thesis by auto
qed

end
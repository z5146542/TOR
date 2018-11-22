theory week01B_demo imports Main begin

text "lambda terms"

term "\<lambda>x. x"


text "alpha"

thm refl

lemma "(\<lambda>x. x) = (\<lambda>y. y)"
  apply (rule refl)
  done


text "eta"

term "\<lambda>x. f x"


text "beta"

term "(\<lambda>x. x y) t"


text {* beta with renaming *}

term "(\<lambda>z. (\<lambda>x. f x z)) x"


text "definitions and unfold"

definition
  c_0 :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "c_0 \<equiv> \<lambda>f x. x"

definition
  c_1 :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "c_1 \<equiv> \<lambda>f x. f x"

definition
  c_2 :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "c_2 \<equiv> \<lambda>f x. f (f x)"

definition
  c_3 :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "c_3 \<equiv> \<lambda>f x. f (f (f x))"

definition
  succ :: "(('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "succ \<equiv> \<lambda>n f x. f (n f x)"

definition
  add :: "(('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 
          ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "add \<equiv> \<lambda>m n f x. m f (n f x)"

definition
  mult :: "(('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>  
          ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "mult \<equiv> \<lambda>m n f x. m (n f) x"


text "unfolding a definition"

lemma "c_0 = (\<lambda>f x. x)"
  apply (unfold c_0_def)
  apply (rule refl)
  done

lemma "succ (succ c_0) = c_2"
  apply (unfold succ_def c_0_def c_2_def)
  apply (rule refl)
  done

lemma "add c_2 c_2 = succ c_3"
  apply (unfold add_def succ_def c_3_def c_2_def)
  apply (rule refl)
  done

lemma "add x c_0 = x"
  apply (unfold add_def c_0_def)
  apply (rule refl)
  done
  
lemma "mult c_1 x = x"
  apply (unfold mult_def c_1_def)
  apply (rule refl)
  done
  
end
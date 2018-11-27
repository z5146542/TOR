theory week04A_demo_simp imports Main begin

text {* Simplification *}

text {* 
Lists: 
  @{term "[]"}       empty list
  @{term "x#xs"}     cons (list with head x and tail xs)
  @{term "xs @ ys"}  append xs and ys
*}

lemma "ys @ [] = []"
apply(simp)
oops 

definition
  a :: "nat list"
where
  "a \<equiv> []"

definition
  b :: "nat list"
where
  "b \<equiv> []"

text {* simp add, rewriting with definitions *}
lemma "xs @ a = xs" 
  apply (simp add: a_def)
  done

text {* simp only *}
lemma "xs @ a = xs"
  using [[simp_trace]]
  apply (simp only: a_def)
  apply simp
  done


lemma ab [simp]: "a = b" by (simp add: a_def b_def)
lemma ba [simp]: "b = a" by simp

text {* simp del, termination *}
lemma "a = []"
  
  (*apply (simp add: a_def)  
   does not terminate *)
  apply (simp add: a_def del: ab) 
  done


text{* Simple assumption: *}
lemma "xs = [] \<Longrightarrow> xs @ ys = ys @ xs @ ys"
  apply simp
  oops

text{* Simplification in assumption: *}
lemma "\<lbrakk> xs @ zs = ys @ xs; [] @ xs = [] @ [] \<rbrakk> \<Longrightarrow> ys = zs"
  apply simp
  done


end
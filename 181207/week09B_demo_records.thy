theory week09B_demo_records
imports Main
begin

record A = a :: nat
           b :: int

term "\<lparr>a = 3,b = 4\<rparr>"
term a
term b
term a_update

(* notice that the name is global; try to give longer names,
     otherwise 'a' is taken for the rest of the theory *)

consts r :: A
term r
term "a r"
consts re :: "unit A_scheme"
consts rf :: "int A_scheme"

term re
term rf

term "A.more"
term "A.more re"
term "A.more rf"
term "A.more rb"

record B = A + c :: "nat list"

consts rb :: B
term rb
term "A.more rb"
term "B.more rb "
term "A.a rb"
term B.more
term A.more

end
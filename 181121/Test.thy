theory Test
  imports Main
begin

declare [[show_types=true]]
term "(1::nat) + a"
term "2 == 5" text {* this evaluates to 'prop' *}
term "Suc" text {* This evaluates to  '"nat" => "nat"' *}
term "True" text {* This evaluates to 'bool' *}
term "a" text {* This evaluates to '`a' *}
term "Succ a b c" text {* This evaluates to '`b' (output of type `b) *}
term "Suc a" text {* This evaluates to 'nat' *}
term "Min" text {* This evaluates to  '`a set => `a'*}
term "Max" text {* This evaluates to  '`a set => `a'*}
term "[a, b, c]" text {* This evaluates to '`a list' *}
term "[True, True]" text {* This evaluates to 'bool list' *}
term "{a, b, c}" text {* This evaluates to '`a set' *}
term "{True, True}" text {* This evaluates to 'bool set' *}
term "Max {3, 5}" text {* This evaluates to '`a' *}

value "(\<lambda>x::nat. x+5) 2" text {* This evaluates to '`a => `a' *}

term "Suc(Suc x)"

datatype tri = high | low | high_impedance

term "a::tri"

declare [[show_types=false]]


end
Require Import Arith.
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.
Parameter max_int:Z.
Definition min_int:Z:=(1-max_int).
Print min_int.
Definition cube (z:Z):Z:=z*z*z.
Print cube.
Check cube.
Definition multi (z:Z)(x:Z):Z:=z*x.
Print multi.
Compute (multi 12 2).
Definition Z_thrice (f:Z->Z)(z:Z):=f(f(f z)).
Print Z_thrice.
Definition plus3:=Z_thrice(fun z:Z=>(z+1)%Z).
Print plus3.
Check plus3.
Compute (plus3 32).
Definition anonymous_fun:=fun (a b c d e:Z)=>a+b+c+d+e.
Print anonymous_fun.
Compute (anonymous_fun 1 2 3 4 5).
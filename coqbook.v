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
Section binomial_def.
  Variables a b:Z.
  Definition binomial (z:Z):=a*z+b.
  Print binomial.
End binomial_def.
Print binomial.

Definition p1:Z->Z:=binomial 5 2.
Print p1.
Compute (p1 3).

Section sum_5_params.
  Variables a b c d e:Z.
  Definition sum_f:=a+b+c+d+e.
End sum_5_params.

Print sum_f.
Compute (sum_f 1 2 3 4 5).

Section h_def.
  Variables a b:Z.
  Let s:Z:=a+b.
  Let d:Z:=a-b.
  Definition h:Z:=s*s+d*d.
End h_def.
Print h.
Check h.

Definition h_2:=fun (a b:Z)=>(a+b)*(a+b)+(a-b)*(a-b).
Print h_2.

(*Eval usage*)

Definition Zsqr(z:Z):Z:=z*z.
Definition my_fun(f:Z->Z)(z:Z):Z:=f (f z).
Eval cbv delta [my_fun Zsqr] in (my_fun Zsqr).
Compute ((my_fun Zsqr) 2). (*2^4*)
Eval cbv delta [my_fun] in (my_fun Zsqr).
(*Eval cbv delta in (my_fun Zsqr).*)

Eval cbv beta delta [my_fun Zsqr] in (my_fun Zsqr).

Eval cbv delta [h_2] in (h_2 32 23).
Eval cbv beta delta [h_2] in (h_2 32 23).
Eval cbv beta zeta delta [h_2] in (h_2 32 23).

Eval cbv delta [h] in (h 32 23).
Eval cbv beta delta [h] in (h 32 23).
Eval cbv beta zeta delta [h] in (h 32 23).

Definition f1:=fun x:Z=>2*x*x+3*x+3.
Eval compute in (f1 2).
Compute (f1 2).
Eval cbv iota beta zeta delta [f1] in (f1 2).


Check Z.
Check 2.
Check Z->Z.
Check nat->nat.
Check f1.
Check (f1 2).
Check Set.
Check Type.
Check (nat->nat:Type).

Section Minimal_propositional_logic.
  Variables P Q R T:Prop.
  Theorem imp_trans:(P->Q)->(Q->R)->P->R.
    Proof.
      intros H H' p.
      apply H'.
      apply H.
      (*apply p.*)
      (*assumption.*)
      exact p.
    Qed.
  Check (P->Q)->(Q->R)->P->R.
  

  
  Section example_of_assumption.
    Hypothesis H:P->Q->R.
    Lemma L1:P->Q->R.
      Proof.
        assumption.
      Qed.
    Theorem delta:(P->P->Q)->P->Q.
      Proof.
        exact (fun (H:P->P->Q)(p:P)=>H p p).
      Qed.
  End example_of_assumption.
  
  Theorem apply_example : (Q->R->T)->(P->Q)->P->R->T.
  Proof.
    intros H H0 p.
    apply H.
    exact (H0 p).
  Qed.
  
  Theorem imp_dist:(P->Q->R)->(P->Q)->(P->R).
    Proof.
      intros H H' p.
      Show 1.
      apply H.
      apply p.
      exact (H' p).
    Qed.
  
  Definition f:(nat->bool)->(nat->bool)->nat->bool.
    intros f1 f2.
    assumption.
  Defined.
  Print f.
    



End Minimal_propositional_logic.

Print imp_dist.

Section section_for_cut_example.
  Variables P Q R T:Prop.
  Hypothesis (H:P->Q) (H0:Q->R) (H1:(P->R)->T->Q) (H2:(P->R)->T).
  
  Theorem cut_example:Q.
    Proof.
      cut (P->R).
      intros H3.
      apply H1;[assumption|apply H2;assumption].
      intros H3.
      apply H0;apply H;assumption.
    Qed.
End section_for_cut_example.
      


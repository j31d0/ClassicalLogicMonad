Definition Lem := (forall Q: Prop, Q \/ ~Q).

Definition C (P: Prop) := Lem -> P.

Lemma c_unit: forall P: Prop, P -> C P.
Proof.
    intros P vP LEM; assumption.
Qed.

Lemma c_bind: forall P Q: Prop, C P -> (P -> C Q) -> C Q.
Proof.
    intros P Q vCP HPQ LEM.
    apply (HPQ (vCP LEM) LEM).
Qed.

Lemma c_prop1: forall (f: Prop -> Prop), (forall P: Prop, C (f P)) -> C (forall P: Prop, f P).
Proof.
    intros f H LEM P.
    apply (H P LEM).
Qed.

Lemma c_prop2: forall (P Q: Prop), (P -> C Q) -> C (P -> Q).
Proof.
    intros P Q HPQ LEM vP.
    apply (HPQ vP LEM).
Qed.

Lemma c_lem: forall P: Prop, C (P \/ ~P).
Proof.
    intros P LEM.
    apply (LEM P).
Qed.

Ltac cremove_0 H X Y Z := let a := fresh "H" in pose proof (c_prop2 _ _ H) as a;
apply (c_bind _ Z) in a; [ assumption | ]; let b := fresh "H" in
intro b; move b before H; clear H; clear a; rename b into H.

Ltac cremove_1 H X Y Z := 
    let a := fresh "H" in assert (X -> Y) as a;
    [ let b := fresh "H" in intro b; apply (c_unit X) in b; apply H in b; assumption
     | clear H; rename a into H ].

Ltac cremove_2 H X Y :=
    apply (c_bind _ Y) in H; [assumption | ]; let a := fresh "H" in
    intro a; move a before H; clear H; rename a into H.


Lemma cremove_hyp: forall P Q: Prop, C (P -> Q) -> C P -> C Q.
Proof.
    intros P Q H1 H2.
    cremove_2 H1 (P -> Q) Q.
    cremove_2 H2 P Q.
    apply H1 in H2. apply c_unit; assumption.
Qed.

Ltac cremove_3 H X Y :=
    let a := fresh "H" in assert (a := cremove_hyp X Y H); move a before H; clear H; rename a into H
.

Ltac cremove := repeat lazymatch goal with
 | [ H: ?X -> C ?Y |- C ?Z ] =>
    cremove_0 H X Y Z
 | [ H: C ?X -> ?Y |- C ?Z ] =>
    cremove_1 H X Y Z
 | [ H: C ?X |- C ?Y ] =>
    cremove_2 H X Y
 | [ |- C (?X -> ?Y) ] =>
    apply (c_prop1 X Y)
 | [ |- ?X -> _ ] => intro
 | [ H: C (?X -> ?Y) |- _ ] =>
    cremove_3 H X Y
end.

Ltac cassumption := lazymatch goal with
 | [ H: ?X |- C ?X ] => apply c_unit; assumption
end.

Ltac capply H := apply (c_unit _ H).
Ltac decided := apply c_unit.

Ltac cdestruct H := cremove; destruct H.
Lemma o_and: forall P Q: Prop, C P /\ C Q -> C (P /\ Q).
Proof.
    intros P Q H.
    destruct H as [ H0 H1 ].
    cremove.
    decided.
    apply (conj H0 H1).
Qed.


Ltac csplit := lazymatch goal with
 | [ |- C (?A /\ ?B) ] => apply (o_and A B); split
end.

Ltac exm P := let a := fresh "H" in pose proof (c_lem P) as a;
  let b := type of a in let c := lazymatch goal with | [ |- C ?Z ] => Z end in cremove_2 a b c; destruct a.

Lemma classic_false: (exists P: Prop, C P /\ ~P) -> C False.
Proof.
    intros H.
    destruct H. destruct H.
    cremove. absurd x; assumption.
Qed.

Lemma classic_not: forall P: Prop, (P -> C False) -> C (~ P).
Proof.
    intros P H.
    exm P.
    apply H in H0.
    cremove; inversion H0.
    cassumption.
Qed.

Lemma o_mp: forall P Q: Prop, C (P -> Q) -> C P -> C Q.
Proof.
    intros P Q H1 H2.
    cremove. specialize (H1 H2). cassumption.
Qed.

Lemma o_fmapd: forall A B P: Prop, C (A \/ B) -> (A -> C P) -> (B -> C P) -> C P.
Proof.
    intros A B P.
    cremove.
    destruct H. capply (H0 H).
    capply (H1 H).
Qed.

Lemma o_dfmapo: forall P A B: Prop, C P -> (P -> C (A \/ B)) -> C (A \/ B).
Proof.
    intros P A B H1 H2.
    cremove.
    capply (H2 H1).
Qed.

Lemma o_dfmapd: forall A B P Q: Prop, C (A \/ B) -> (A -> C (P \/ Q)) -> (B -> C (P \/ Q)) -> C (P \/ Q).
Proof.
    intros A B P Q H1 H2 H3.
    cremove.
    destruct H1.
    capply (H2 H).
    capply (H3 H).
Qed.

Lemma o_fmapo_c: forall P Q: Prop, (P -> C Q) -> C P -> C Q.
Proof.
intros P Q H R.
cremove.
capply (H R).
Qed.

Lemma  dis_elim: forall A B P: Prop, C (A \/ B) -> C (A -> P) -> C (B -> P) -> C P.
Proof.
intros A B P H0 H1 H2.
cremove.
destruct H0. pose proof (H1 H). capply H0.
pose proof (H2 H). capply H0.
Qed.

Lemma o_red: forall P: Prop, C (C P) -> C P.
Proof.
    intros P H.
    cremove.
    assumption.
Qed.

Lemma o_mp_inv': forall P Q: Prop, (C P -> C Q) -> C (P -> Q).
Proof.
    intros P Q H1.
    cremove.
    cassumption.
Qed.

Lemma c_mp: forall A B P Q: Prop, C (A \/ B) -> C (A -> P) -> C (B -> Q) -> C (P \/ Q).
Proof.
    intros A B P Q D Cap Cbq.
    cremove.
    destruct D.
    specialize (Cap H); capply (or_introl Q Cap).
    specialize (Cbq H); capply (or_intror P Cbq).
Qed.

Lemma PP: forall P Q: Prop, (P -> Q) /\ (~P -> Q) -> C Q.
Proof.
    intros P Q Hpq.
    pose proof (c_lem P).
    cremove. decided.
    destruct H.
    destruct Hpq as [ Hpq _ ]. apply (Hpq H).
    destruct Hpq as [ _ Hpq ]. apply (Hpq H).
Qed.

Lemma NNPP: forall P: Prop, ~~P -> C P.
Proof.
intros P Hnnp.
exm P; decided.
assumption.
specialize (Hnnp H); inversion Hnnp.
Qed.


Lemma Peirce: forall P: Prop, ((P -> False) -> P) -> C P.
Proof.
intros P H.
exm P; decided. assumption.
apply H in H0. assumption.
Qed.

Lemma not_imply_elim: forall P Q: Prop, ~ (P -> Q) -> C P.
Proof.
intros P Q H. apply NNPP. red.
intro. apply H. intro. absurd P; assumption.
Qed.

Lemma not_imply_elim2: forall P Q: Prop, ~ (P -> Q) -> C (~ Q).
Proof.
intros P Q H. exm Q; decided. assert False. apply H. intro; assumption.
inversion H1. assumption.
Qed.

Lemma imply_to_or: forall P Q: Prop, (P -> Q) -> C (~ P \/ Q).
Proof.
intros P Q H. exm P; decided. right. apply (H H0).
left. assumption.
Qed.

Lemma imply_to_and: forall P Q: Prop, ~ (P -> Q) -> C (P /\ ~ Q).
Proof.
intros P Q H.
csplit. apply (not_imply_elim P Q H). apply (not_imply_elim2 P Q H).
Qed.

Lemma or_to_imply: forall P Q: Prop, ~ P \/ Q -> P -> C Q.
Proof.
intros P Q H H1.
destruct H.
absurd P; assumption.
cassumption.
Qed.

Lemma not_and_or: forall P Q: Prop, ~ (P /\ Q) -> C ( ~P \/ ~Q ).
Proof.
intros P Q H.
exm P. exm Q. pose proof (conj H0 H1). absurd (P /\ Q); assumption.
all: decided. right; assumption. left; assumption.
Qed.

Lemma not_all_not_ex: forall (U: Type) (P: U -> Prop) , ~(forall n: U, ~ P n) -> C (exists n: U, P n).
Proof.
intros U P H.
apply NNPP.
intro abs.
apply H.
intros n H2.
apply abs; exists n; exact H2.
Qed.


Lemma not_all_ex_not_p: forall (O: Prop -> Prop) , ~(forall P: Prop, O P) -> C (exists P: Prop, ~ O P).
Proof.
intros O H.
pose proof (not_all_not_ex _ (fun x => ~ O x)). cremove. apply c_unit in H0.
apply (cremove_hyp _ _ H0).
apply classic_not.
intro Hall.
unfold not in H.
apply c_unit in H.
cremove_3 H (forall n : Prop, O n) False.
apply H. cremove. apply c_prop1. intro n. specialize (Hall n).
apply NNPP in Hall. assumption.
Qed.

Inductive CI: Prop -> Prop :=
 | ci_unit: forall P: Prop, P -> CI P
 | ci_prop1: forall (f: Prop -> Prop), (forall P: Prop, CI (f P)) -> CI (forall P: Prop, f P)
 | ci_prop2: forall (P Q: Prop), (P -> CI Q) -> CI (P -> Q)
 | ci_bind: forall P Q: Prop, CI P -> (P -> CI Q) -> CI Q
 | ci_lem: forall P: Prop, CI (P \/ ~P)
.



Lemma if_exm: forall P: Prop, (forall Q: Prop, Q \/ ~ Q) -> CI P -> P.
  Proof.
      intros P H CI.
      induction CI.
      assumption.
      assumption.
      assumption.
      apply (H1 IHCI).
      apply (H P).
Qed.

Ltac ciremove_0 H X Y Z := let a := fresh "H" in pose proof (ci_prop2 _ _ H) as a;
apply (ci_bind _ Z) in a; [ assumption | ]; let b := fresh "H" in
intro b; move b before H; clear H; clear a; rename b into H.

Ltac ciremove_1 H X Y Z := 
    let a := fresh "H" in assert (X -> Y) as a;
    [ let b := fresh "H" in intro b; apply (ci_unit X) in b; apply H in b; assumption
     | clear H; rename a into H ].

Ltac ciremove_2 H X Y :=
    apply (ci_bind _ Y) in H; [assumption | ]; let a := fresh "H" in
    intro a; move a before H; clear H; rename a into H.


Lemma ciremove_hyp: forall P Q: Prop, CI (P -> Q) -> CI P -> CI Q.
Proof.
    intros P Q H1 H2.
    ciremove_2 H1 (P -> Q) Q.
    ciremove_2 H2 P Q.
    apply H1 in H2. apply ci_unit; assumption.
Qed.

Ltac ciremove_3 H X Y :=
    let a := fresh "H" in assert (a := ciremove_hyp X Y H); move a before H; clear H; rename a into H
.

Ltac ciremove := repeat lazymatch goal with
 | [ H: ?X -> CI ?Y |- CI ?Z ] =>
    ciremove_0 H X Y Z
 | [ H: CI ?X -> ?Y |- CI ?Z ] =>
    ciremove_1 H X Y Z
 | [ H: CI ?X |- CI ?Y ] =>
    ciremove_2 H X Y
 | [ |- CI (?X -> ?Y) ] =>
    apply (ci_prop1 X Y)
 | [ |- ?X -> _ ] => intro
 | [ H: CI (?X -> ?Y) |- _ ] =>
    ciremove_3 H X Y
end.

Ltac ciassumption := lazymatch goal with
 | [ H: ?X |- CI ?X ] => apply ci_unit; assumption
end.

Ltac ciapply H := apply (ci_unit _ H).
Ltac cidecided := apply ci_unit.

Ltac cidestruct H := ciremove; destruct H.
Lemma oi_and: forall P Q: Prop, CI P /\ CI Q -> CI (P /\ Q).
Proof.
    intros P Q H.
    destruct H as [ H0 H1 ].
    ciremove.
    cidecided.
    apply (conj H0 H1).
Qed.


Ltac cisplit := lazymatch goal with
 | [ |- CI (?A /\ ?B) ] => apply (oi_and A B); split
end.

Ltac ciexm P := let a := fresh "H" in pose proof (ci_lem P) as a;
  let b := type of a in let c := lazymatch goal with | [ |- CI ?Z ] => Z end in ciremove_2 a b c; destruct a.

Lemma ci_false: (exists P: Prop, CI P /\ ~P) -> CI False.
Proof.
    intros H.
    destruct H. destruct H.
    ciremove. absurd x; assumption.
Qed.

Lemma ci_not: forall P: Prop, (P -> CI False) -> CI (~ P).
Proof.
    intros P H.
    ciexm P.
    apply H in H0.
    ciremove; inversion H0.
    ciassumption.
Qed.

Lemma oi_mp: forall P Q: Prop, CI (P -> Q) -> CI P -> CI Q.
Proof.
    intros P Q H1 H2.
    ciremove. specialize (H1 H2). ciassumption.
Qed.

Lemma oi_fmapd: forall A B P: Prop, CI (A \/ B) -> (A -> CI P) -> (B -> CI P) -> CI P.
Proof.
    intros A B P.
    ciremove.
    destruct H. ciapply (H0 H).
    ciapply (H1 H).
Qed.

Lemma oi_dfmapo: forall P A B: Prop, CI P -> (P -> CI (A \/ B)) -> CI (A \/ B).
Proof.
    intros P A B H1 H2.
    ciremove.
    ciapply (H2 H1).
Qed.

Lemma oi_dfmapd: forall A B P Q: Prop, CI (A \/ B) -> (A -> CI (P \/ Q)) -> (B -> CI (P \/ Q)) -> CI (P \/ Q).
Proof.
    intros A B P Q H1 H2 H3.
    ciremove.
    destruct H1.
    ciapply (H2 H).
    ciapply (H3 H).
Qed.

Lemma oi_fmapo_c: forall P Q: Prop, (P -> CI Q) -> CI P -> CI Q.
Proof.
intros P Q H R.
ciremove.
ciapply (H R).
Qed.

Lemma  disi_elim: forall A B P: Prop, CI (A \/ B) -> CI (A -> P) -> CI (B -> P) -> CI P.
Proof.
intros A B P H0 H1 H2.
ciremove.
destruct H0. pose proof (H1 H). ciapply H0.
pose proof (H2 H). ciapply H0.
Qed.

Lemma oi_red: forall P: Prop, CI (CI P) -> CI P.
Proof.
    intros P H.
    ciremove.
    ciassumption.
Qed.

Lemma oi_mp_inv': forall P Q: Prop, (CI P -> CI Q) -> CI (P -> Q).
Proof.
    intros P Q H1.
    ciremove.
    ciassumption.
Qed.

Lemma ci_mp: forall A B P Q: Prop, CI (A \/ B) -> CI (A -> P) -> CI (B -> Q) -> CI (P \/ Q).
Proof.
    intros A B P Q D Cap Cbq.
    ciremove.
    destruct D.
    specialize (Cap H); ciapply (or_introl Q Cap).
    specialize (Cbq H); ciapply (or_intror P Cbq).
Qed.

Lemma PPi: forall P Q: Prop, (P -> Q) /\ (~P -> Q) -> CI Q.
Proof.
    intros P Q Hpq.
    pose proof (ci_lem P).
    ciremove. cidecided.
    destruct H.
    destruct Hpq as [ Hpq _ ]. apply (Hpq H).
    destruct Hpq as [ _ Hpq ]. apply (Hpq H).
Qed.

Lemma NNPPi: forall P: Prop, ~~P -> CI P.
Proof.
intros P Hnnp.
ciexm P; cidecided.
assumption.
specialize (Hnnp H); inversion Hnnp.
Qed.


Lemma Peircei: forall P: Prop, ((P -> False) -> P) -> CI P.
Proof.
intros P H.
ciexm P; cidecided. assumption.
apply H in H0. assumption.
Qed.

Lemma not_imply_elimi: forall P Q: Prop, ~ (P -> Q) -> CI P.
Proof.
intros P Q H. apply NNPPi. red.
intro. apply H. intro. absurd P; assumption.
Qed.

Lemma not_imply_elim2i: forall P Q: Prop, ~ (P -> Q) -> CI (~ Q).
Proof.
intros P Q H. ciexm Q; cidecided. assert False. apply H. intro; assumption.
inversion H1. assumption.
Qed.

Lemma imply_to_ori: forall P Q: Prop, (P -> Q) -> CI (~ P \/ Q).
Proof.
intros P Q H. ciexm P; cidecided. right. apply (H H0).
left. assumption.
Qed.

Lemma imply_to_andi: forall P Q: Prop, ~ (P -> Q) -> CI (P /\ ~ Q).
Proof.
intros P Q H.
cisplit. apply (not_imply_elimi P Q H). apply (not_imply_elim2i P Q H).
Qed.

Lemma or_to_implyi: forall P Q: Prop, ~ P \/ Q -> P -> CI Q.
Proof.
intros P Q H H1.
destruct H.
absurd P; assumption.
ciassumption.
Qed.

Lemma not_and_ori: forall P Q: Prop, ~ (P /\ Q) -> CI ( ~P \/ ~Q ).
Proof.
intros P Q H.
ciexm P. ciexm Q. pose proof (conj H0 H1). absurd (P /\ Q); assumption.
all: cidecided. right; assumption. left; assumption.
Qed.

Lemma not_all_not_exi: forall (U: Type) (P: U -> Prop) , ~(forall n: U, ~ P n) -> CI (exists n: U, P n).
Proof.
intros U P H.
apply NNPPi.
intro abs.
apply H.
intros n H2.
apply abs; exists n; exact H2.
Qed.


Lemma not_all_ex_not_pi: forall (O: Prop -> Prop) , ~(forall P: Prop, O P) -> CI (exists P: Prop, ~ O P).
Proof.
intros O H.
pose proof (not_all_not_exi _ (fun x => ~ O x)). ciremove. apply ci_unit in H0.
apply (ciremove_hyp _ _ H0).
apply ci_not.
intro Hall.
unfold not in H.
apply ci_unit in H.
ciremove_3 H (forall n : Prop, O n) False.
apply H. ciremove. apply ci_prop1. intro n. specialize (Hall n).
apply NNPPi in Hall. assumption.
Qed.

Lemma using_CI: forall A : Prop, ((forall P: Prop, CI P -> P) -> A) -> CI A.
Proof.
    intros A H.
    ciexm (forall P: Prop, CI P -> P).
    cidecided. apply (H H0).
    assert (CI (exists P: Prop, ~ (CI P -> P))).
    apply not_all_ex_not_pi. assumption.
    cidestruct H1.
    apply imply_to_andi in H1.
    cidestruct H1.
    ciremove. absurd x; assumption.
Qed.

Lemma using_ciexm: forall A: Prop, (Lem -> A) -> CI A.
Proof.
    intros A H.
    apply using_CI.
    intro Hctoi.
    assert (forall P: Prop, P \/ ~P).
    intro P.
    pose proof (ci_lem P). specialize (Hctoi (P \/ ~P) H0). assumption.
    apply (H H0).
Qed.


  
Theorem equiv_C_CI: forall P: Prop, C P <-> CI P.
Proof.
    split; intro H.
    apply using_ciexm. assumption.
    intro Hciexm. apply (if_exm _ Hciexm H).
Qed.


Definition weak_lem :=
(fun (P : Prop) (vnP : P -> False) (vnnP : ~ P -> False) => vnnP vnP)
: forall (P: Prop), (P -> False) -> (~P -> False) -> False.

Definition notnot_lem:= (fun P : Prop =>
 (fun H : ~ (P \/ ~ P) =>
  weak_lem P (fun vP : P => H (or_introl vP)) (fun vnP : ~ P => H (or_intror vnP)))
 : ~ ~ (P \/ ~ P)).


Lemma not_all_not_not_ex: forall (U: Type) (P: U -> Prop) , ~(forall n: U, ~ P n) -> ~~(exists n: U, P n).
Proof.
intros U P H.
intro abs.
apply H.
intros n H2.
apply abs; exists n; exact H2.
Qed.

Lemma weak_lem_ex: forall (U: Type) (P: U -> Prop), ((forall n: U, ~ P n) -> False) -> ((exists n: U, P n) -> False) -> False.
Proof.
intros U P.
intros HF HE.
apply (weak_lem (exists n: U, P n)).
assumption.
apply not_all_not_not_ex.
assumption.
Qed.

Lemma forall_transfer: forall (U: Type) (P: U -> Prop) (R: Prop), (exists n: U, True) -> (forall n: U, P n -> R) -> (forall n: U, P n) -> R.
Proof.
intros U P R eU H1 H2.
destruct eU.
specialize (H1 x).
specialize (H2 x).
apply (H1 H2).
Qed.

Lemma atp: forall P R: Prop, ((P -> R) -> R) -> ~P -> R.
intros P R hprr hnp.
assert (P -> R).
intro K. assert False. apply (hnp K). destruct H.
apply (hprr H).
Qed.




Lemma not_ex_not_not_all: forall (U: Type) (P: U -> Prop) , ~(exists n: U, ~ P n)  -> (forall n: U, ~~ P n) .
Proof.
intros U P H n pn.
apply H.
exists n.
assumption.
Qed.


Definition DNS := (forall (O: Prop -> Prop), (forall Q: Prop, ~~ (O Q)) -> ~~ (forall Q: Prop, O Q)).

Definition DN (P: Prop) := DNS -> ~~ P.

Definition DNRel (P Q: Prop) := P = Q.

Definition CDNProp : CI DNS.
Proof.
apply using_CI.
intro Hctoi.
intros O P.
enough (forall Q: Prop, O Q).
intro K. apply (K H).
intro vQ.
specialize (P vQ).
apply (Hctoi _ (NNPPi _ P)).
Qed.

Lemma using_nn: forall A: Prop, DN A -> CI A.
Proof.
  intros A H.
  apply using_CI.
  intro Hctoi.
  apply (Hctoi _ (NNPPi _ (H (Hctoi _ CDNProp)))).
Qed.

Lemma DNLem: DN Lem .
Proof.
intro H.
apply (H _).
intro P.
apply notnot_lem.
Qed.

Lemma nn_using: forall A: Prop, CI A ->
  DN A.
Proof.
intros A H HI. intro K.
apply (weak_lem (forall P: Prop, P \/ ~P)).
intro Lem. apply (K (if_exm A Lem H)).
apply (DNLem HI).
Qed.


Lemma equiv_DN_CI: forall A: Prop, DN A <-> CI A.
Proof.
    intro A. split. apply using_nn. apply nn_using.
Qed.

Lemma NNmp: forall P Q: Prop, (P -> Q) -> ~~P -> ~~Q.
Proof.
intros P Q H nnP K.
apply (weak_lem P).
intro vP. apply (K (H vP)).
intro nP. apply (nnP nP).
Qed.

Lemma NNNN: forall P: Prop, ~~~~P -> ~~P.
Proof.
intros P H.
intro nP.
apply (weak_lem (~~P)).
intro nnnP. apply (nnnP nP).
intro nnnP. apply (H nnnP).
Qed.

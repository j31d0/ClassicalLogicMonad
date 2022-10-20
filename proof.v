Definition Lem := (forall Q: Prop, Q \/ ~Q).

Definition C' (P: Prop) := Lem -> P.

Inductive C: Prop -> Prop :=
 | o_unit: forall P: Prop, P -> C P
 | o_mp_inv: forall (O: Prop -> Prop), (forall P: Prop, C (O P)) -> C (forall P: Prop, O P)
 | o_mp_inv2: forall (P Q: Prop), (P -> C Q) -> C (P -> Q)
 | o_fmapo: forall P Q: Prop, C P -> (P -> C Q) -> C Q
 | o_em: forall P: Prop, C (P \/ ~P)
.

Ltac rclassic_0 H X Y Z := let a := fresh "H" in pose proof (o_mp_inv2 _ _ H) as a;
apply (o_fmapo _ Z) in a; [ assumption | ]; let b := fresh "H" in
intro b; move b before H; clear H; clear a; rename b into H.

Ltac rclassic_1 H X Y Z := 
    let a := fresh "H" in assert (X -> Y) as a;
    [ let b := fresh "H" in intro b; apply (o_unit X) in b; apply H in b; assumption
     | clear H; rename a into H ].

Ltac rclassic_2 H X Y :=
    apply (o_fmapo _ Y) in H; [assumption | ]; let a := fresh "H" in
    intro a; move a before H; clear H; rename a into H.


Lemma o_hyp: forall P Q: Prop, C (P -> Q) -> C P -> C Q.
Proof.
    intros P Q H1 H2.
    rclassic_2 H1 (P -> Q) Q.
    rclassic_2 H2 P Q.
    apply H1 in H2. apply o_unit; assumption.
Qed.

Ltac rclassic_3 H X Y :=
    let a := fresh "H" in assert (a := o_hyp X Y H); move a before H; clear H; rename a into H
.

Ltac rclassic := repeat lazymatch goal with
 | [ H: ?X -> C ?Y |- C ?Z ] =>
    rclassic_0 H X Y Z
 | [ H: C ?X -> ?Y |- C ?Z ] =>
    rclassic_1 H X Y Z
 | [ H: C ?X |- C ?Y ] =>
    rclassic_2 H X Y
 | [ |- C (?X -> ?Y) ] =>
    apply (o_mp_inv X Y)
 | [ |- ?X -> _ ] => intro
 | [ H: C (?X -> ?Y) |- _ ] =>
    rclassic_3 H X Y
end.

Ltac cassumption := lazymatch goal with
 | [ H: ?X |- C ?X ] => apply o_unit; assumption
end.

Ltac capply H := apply (o_unit _ H).
Ltac decided := apply o_unit.

Ltac rdestruct H := rclassic; destruct H.
Lemma o_and: forall P Q: Prop, C P /\ C Q -> C (P /\ Q).
Proof.
    intros P Q H.
    destruct H as [ H0 H1 ].
    rclassic.
    decided.
    apply (conj H0 H1).
Qed.


Ltac csplit := lazymatch goal with
 | [ |- C (?A /\ ?B) ] => apply (o_and A B); split
end.

Ltac exm P := let a := fresh "H" in pose proof (o_em P) as a;
  let b := type of a in let c := lazymatch goal with | [ |- C ?Z ] => Z end in rclassic_2 a b c; destruct a.


Lemma if_exm: forall P: Prop, (forall Q: Prop, Q \/ ~ Q) -> C P -> P.
Proof.
    intros P H C.
    induction C.
    assumption.
    assumption.
    assumption.
    apply (H1 IHC).
    apply (H P).
Qed.


Lemma classic_false: (exists P: Prop, C P /\ ~P) -> C False.
Proof.
    intros H.
    destruct H. destruct H.
    rclassic. absurd x; assumption.
Qed.

Lemma classic_not: forall P: Prop, (P -> C False) -> C (~ P).
Proof.
    intros P H.
    exm P.
    apply H in H0.
    rclassic; inversion H0.
    cassumption.
Qed.

Lemma o_mp: forall P Q: Prop, C (P -> Q) -> C P -> C Q.
Proof.
    intros P Q H1 H2.
    rclassic. specialize (H1 H2). cassumption.
Qed.

Lemma o_fmapd: forall A B P: Prop, C (A \/ B) -> (A -> C P) -> (B -> C P) -> C P.
Proof.
    intros A B P.
    rclassic.
    destruct H. capply (H0 H).
    capply (H1 H).
Qed.

Lemma o_dfmapo: forall P A B: Prop, C P -> (P -> C (A \/ B)) -> C (A \/ B).
Proof.
    intros P A B H1 H2.
    rclassic.
    capply (H2 H1).
Qed.

Lemma o_dfmapd: forall A B P Q: Prop, C (A \/ B) -> (A -> C (P \/ Q)) -> (B -> C (P \/ Q)) -> C (P \/ Q).
Proof.
    intros A B P Q H1 H2 H3.
    rclassic.
    destruct H1.
    capply (H2 H).
    capply (H3 H).
Qed.

Lemma o_fmapo_c: forall P Q: Prop, (P -> C Q) -> C P -> C Q.
Proof.
intros P Q H R.
rclassic.
capply (H R).
Qed.

Lemma  dis_elim: forall A B P: Prop, C (A \/ B) -> C (A -> P) -> C (B -> P) -> C P.
Proof.
intros A B P H0 H1 H2.
rclassic.
destruct H0. pose proof (H1 H). capply H0.
pose proof (H2 H). capply H0.
Qed.

Lemma o_red: forall P: Prop, C (C P) -> C P.
Proof.
    intros P H.
    rclassic.
    cassumption.
Qed.

Lemma o_mp_inv': forall P Q: Prop, (C P -> C Q) -> C (P -> Q).
Proof.
    intros P Q H1.
    rclassic.
    cassumption.
Qed.

Lemma c_mp: forall A B P Q: Prop, C (A \/ B) -> C (A -> P) -> C (B -> Q) -> C (P \/ Q).
Proof.
    intros A B P Q D Cap Cbq.
    rclassic.
    destruct D.
    specialize (Cap H); capply (or_introl Q Cap).
    specialize (Cbq H); capply (or_intror P Cbq).
Qed.

Lemma PP: forall P Q: Prop, (P -> Q) /\ (~P -> Q) -> C Q.
Proof.
    intros P Q Hpq.
    pose proof (o_em P).
    rclassic. decided.
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
pose proof (not_all_not_ex _ (fun x => ~ O x)). rclassic. apply o_unit in H0.
apply (o_hyp _ _ H0).
apply classic_not.
intro Hall.
unfold not in H.
apply o_unit in H.
rclassic_3 H (forall n : Prop, O n) False.
apply H. rclassic. apply o_mp_inv. intro n. specialize (Hall n).
apply NNPP in Hall. assumption.
Qed.

Lemma using_classical: forall A : Prop, ((forall P: Prop, C P -> P) -> A) -> C A.
Proof.
    intros A H.
    exm (forall P: Prop, C P -> P).
    decided. apply (H H0).
    assert (C (exists P: Prop, ~ (C P -> P))).
    apply not_all_ex_not_p. assumption.
    rdestruct H1.
    apply imply_to_and in H1.
    rdestruct H1.
    rclassic. absurd x; assumption.
Qed.

Lemma using_exm: forall A: Prop, (Lem -> A) -> C A.
Proof.
    intros A H.
    apply using_classical.
    intro Hctoi.
    assert (forall P: Prop, P \/ ~P).
    intro P.
    pose proof (o_em P). specialize (Hctoi (P \/ ~P) H0). assumption.
    apply (H H0).
Qed.

Theorem equiv_exm: forall P: Prop, C P <-> C' P.
Proof.
    split; intro H.
    intro Hexm. apply (if_exm _ Hexm H).
    apply using_exm. assumption.
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


Definition DNProp := (forall (O: Prop -> Prop), (forall Q: Prop, ~~ (O Q)) -> ~~ (forall Q: Prop, O Q)).

Definition DN (P: Prop) := DNProp -> ~~ P.

Definition DNRel (P Q: Prop) := P = Q.

Definition CDNProp : C DNProp.
Proof.
apply using_classical.
intro Hctoi.
intros O P.
enough (forall Q: Prop, O Q).
intro K. apply (K H).
intro vQ.
specialize (P vQ).
apply (Hctoi _ (NNPP _ P)).
Qed.

Lemma using_nn: forall A: Prop, DN A -> C A.
Proof.
  intros A H.
  apply using_classical.
  intro Hctoi.
  apply (Hctoi _ (NNPP _ (H (Hctoi _ CDNProp)))).
Qed.

Lemma DNLem: DN Lem .
Proof.
intro H.
apply (H _).
intro P.
apply notnot_lem.
Qed.

Lemma nn_using: forall A: Prop, C A ->
  DN A.
Proof.
intros A H HI. intro K.
apply (weak_lem (forall P: Prop, P \/ ~P)).
intro Lem. apply (K (if_exm A Lem H)).
apply (DNLem HI).
Qed.


Lemma equiv_dn: forall A: Prop, DN A <-> C A.
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

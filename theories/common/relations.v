From simuliris.common Require Import
  prelude.

Section relation.
  Context `{R : relation X}.

  Lemma Acc_tc x :
    Acc R x →
    Acc (tc R) x.
  Proof.
    intros Hx. induction Hx. econstructor.
    intros y Hy. induction Hy.
    - eauto.
    - eapply Acc_inv.
      + eapply IHHy; done.
      + eauto using tc_once.
  Qed.
  Lemma tc_wf :
    wf R →
    wf (tc R).
  Proof.
    intros ? ?**. eauto using Acc_tc.
  Qed.
End relation.

From iris.algebra Require Import
  cmra. (* Op *)

From tmc.common Require Import
  prelude.
From tmc.language Require Export
  lang.

Section LangCtx.
  Context (expr ctx : Type).

  Section LangCtxMixin.
    Context `{Empty ctx} `{Op ctx}.
    Context `{LookupTotal expr expr ctx}.
    Implicit Types e : expr.
    Implicit Types C : ctx.

    Record LangCtxMixin := {
      lang_ctx_mixin_comp_assoc :
        Assoc (=) (@op ctx _) ;
      lang_ctx_mixin_fill_empty e :
        (@empty ctx _) !!! e = e ;
      lang_ctx_mixin_fill_comp C1 C2 e :
        (C1 ⋅ C2) !!! e = C1 !!! (C2 !!! e) ;
    }.
  End LangCtxMixin.

  Class LangCtx := {
    lang_ctx_empty :> Empty ctx ;
    lang_ctx_comp :> Op ctx ;
    lang_ctx_fill :> LookupTotal expr expr ctx ;
    lang_ctx_mixin : LangCtxMixin ;
  }.
End LangCtx.
Global Arguments Build_LangCtxMixin {_ _ _ _ _} _ _ _ : assert.
Global Arguments Build_LangCtx {_ _ _ _ _} _ : assert.

Class LangCtxItem expr ctxi :=
  lang_ctx_item_fill :> LookupTotal expr expr ctxi.

Section lang_ctx_of_lang_ctx_item.
  Context {expr ctxi : Type}.
  Context `(LangCtxItem expr ctxi).
  Let ctx := list ctxi.

  Instance : Empty ctx := [].
  Instance : Op ctx := flip (++).
  Instance : LookupTotal expr expr ctx := foldl (!!!).

  Program Global Instance lang_ctx_of_lang_ctx_item : LangCtx expr ctx := {}.
  Next Obligation.
    constructor.
    - intros ?. eauto using app_assoc.
    - auto.
    - eauto using foldl_app.
  Qed.
End lang_ctx_of_lang_ctx_item.

Section LangECtx.
  Context (Λ : lang) (ctx : Type).
  Implicit Types K : ctx.

  Class LangECtx := {
    lang_ectx_lang_ctx :> LangCtx (expr Λ) ctx ;
    lang_ectx_lang_frame K :> LangFrame (K !!!.) ;
  }.
End LangECtx.

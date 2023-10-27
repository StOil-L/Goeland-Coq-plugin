(* PROOF FOUND *)
(* CONTEXT BEGIN *)
Add LoadPath "/mnt/c/Users/loren/Documents/Travail/Goeland-Coq-plugin/coq-demo" as Goeland.
Require Import Goeland.goeland.
Parameter goeland_U : Set.
Parameter goeland_E : goeland_U.
Parameter a : Prop.
Parameter b : Prop.
(* CONTEXT END *)
(* PROOF BEGIN *)
Theorem pb2 : ((a -> b) -> a) -> a.
Proof.
apply NNPP. intro goeland_G.
apply (goeland_notimply_s _ _ goeland_G). goeland_intro goeland_H1. goeland_intro goeland_H2.
apply (goeland_imply_s _ _ goeland_H1); [ goeland_intro goeland_H3 | goeland_intro goeland_H4 ].
apply (goeland_notimply_s _ _ goeland_H3). goeland_intro goeland_H4. goeland_intro goeland_H5.
exact (goeland_H2 goeland_H4).
exact (goeland_H2 goeland_H4).
Qed.
(* PROOF END *)
From refinedc.typing Require Import typing.
From refinedc.project.t01_basic.src.code Require Import generated_code.
From refinedc.project.t01_basic.src.code Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [src/code.c]. *)
Section proof_int_id2.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [int_id2]. *)
  Lemma type_int_id2 :
    ⊢ typed_function impl_int_id2 type_of_int_id2.
  Proof.
    Local Open Scope printing_sugar.
    start_function "int_id2" (n) => arg_a.
    prepare_parameters (n).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "int_id2" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "int_id2".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "int_id2".
  Qed.
End proof_int_id2.

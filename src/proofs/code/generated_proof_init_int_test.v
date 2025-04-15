From refinedc.typing Require Import typing.
From refinedc.project.t01_basic.src.code Require Import generated_code.
From refinedc.project.t01_basic.src.code Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [src/code.c]. *)
Section proof_init_int_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [init_int_test]. *)
  Lemma type_init_int_test (global_init_int : loc) :
    global_init_int ◁ᵥ global_init_int @ function_ptr type_of_init_int -∗
    typed_function (impl_init_int_test global_init_int) type_of_init_int_test.
  Proof.
    Local Open Scope printing_sugar.
    start_function "init_int_test" (p) => arg_out local_i.
    prepare_parameters (p).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init_int_test" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "init_int_test".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "init_int_test".
  Qed.
End proof_init_int_test.

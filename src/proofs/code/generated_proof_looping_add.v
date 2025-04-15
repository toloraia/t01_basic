From refinedc.typing Require Import typing.
From refinedc.project.t01_basic.src.code Require Import generated_code.
From refinedc.project.t01_basic.src.code Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [src/code.c]. *)
Section proof_looping_add.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [looping_add]. *)
  Lemma type_looping_add :
    ⊢ typed_function impl_looping_add type_of_looping_add.
  Proof.
    Local Open Scope printing_sugar.
    start_function "looping_add" ([va vb]) => arg_a arg_b.
    prepare_parameters (va vb).
    split_blocks ((
      <[ "#1" :=
        ∃ acc : Z,
        arg_a ◁ₗ (acc @ (int (i32))) ∗
        arg_b ◁ₗ ((va + vb - acc) @ (int (i32))) ∗
        ⌜0 <= acc⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "looping_add" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "looping_add" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "looping_add".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "looping_add".
  Qed.
End proof_looping_add.

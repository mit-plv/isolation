Require Import Koika.Common.
Require Import Koika.Environments.
Require Import Koika.Syntax.
Require Import Koika.Parsing.

Section Maybe.
  Context (id: nat).
  Context (data_sz: nat).

  Definition FIELD_maybe_valid := 0.
  Definition FIELD_maybe_data := 1.

  Definition STRUCT_maybe_fields :=
    [(_StructField "valid" FIELD_maybe_valid, 1)
    ;(_StructField "data" FIELD_maybe_data, data_sz)
    ].


  Definition STRUCT_maybe :=
    {| struct_name := id;
       struct_fields := STRUCT_maybe_fields
    |}.

  Definition invalid : action :=
    {{ struct id {FIELD_maybe_valid := Ob~0 }
    }}.

  Definition valid (v: action): action :=
    {{ struct id {FIELD_maybe_valid := Ob~1;
                  FIELD_maybe_data := `v`
                 }
    }}.

End Maybe.

Require Import Util Get.

Ltac stuck :=
  let A := fresh "A" in let v := fresh "v" in intros [v A]; inv A; repeat get_functional; isabsurd.

Ltac stuck2 :=
  let A := fresh "A" in
  let v := fresh "v" in
  let evt := fresh "evt" in
  intros [v [evt A]]; inv A; repeat get_functional; isabsurd.

module Mrdt

open FStar.List.Tot

class mrdt t o  = {
      apply_op : t -> o -> t;
      apply_tr : t -> list o -> t
  }

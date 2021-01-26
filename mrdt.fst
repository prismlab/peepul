module Mrdt

open FStar.List.Tot

class mrdt (state:eqtype) (operation:eqtype) = {
  apply_op : state -> operation -> state;
}

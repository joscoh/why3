open BinNums

type 'a coq_Countable = { encode : ('a -> positive);
                          decode : (positive -> 'a option) }


type ('s, 't) state = { runState : ('s -> 't * 's) }

all:
	opam init
	opam install alt-ergo
	eval `opam config env`
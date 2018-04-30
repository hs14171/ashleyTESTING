all:
	opam init
	eval `opam config env`
	opam install alt-ergo
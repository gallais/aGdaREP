COMPILEDIR=__compile

all:
	agda -i . -c --compile-dir=${COMPILEDIR} aGdaREP.agda

clean:
	rm -rf ${COMPILEDIR}
	find . -name "*.agdai" | xargs rm

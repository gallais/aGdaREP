AGDA_EXEC ?= agda
COMPILEDIR=__compile

all:
	${AGDA_EXEC} -i . -c --compile-dir=${COMPILEDIR} aGdaREP.agda

clean:
	rm -rf ${COMPILEDIR}
	find . -name "*.agdai" | xargs rm

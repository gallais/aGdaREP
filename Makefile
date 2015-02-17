STDLIB=~/languages/agda/libs/agda-stdlib/src/
COMPILEDIR=__compile

all:
	agda -i . -i ${STDLIB} -c --compile-dir=${COMPILEDIR} aGdaREP.agda

clean:
	rm -rf ${COMPILEDIR}
	find . -name "*.agdai" | xargs rm

STDLIB=~/languages/agda/libs/agda-stdlib/src/

all:
	agda -i . -i ${STDLIB} -c aGdaREP.agda

clean:
	rm -rf MAlonzo/
	rm -f aGdaREP
	find . -name "*.agdai" | xargs rm

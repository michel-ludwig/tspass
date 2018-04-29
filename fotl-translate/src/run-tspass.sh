#!/bin/sh

function showUsage {
	echo "$0 [<options for \"fotl-translate\">] <input file> [--tspass <options for \"TSPASS\">]"
}

if [ "$#" == "0" ]
then
	showUsage
	exit
fi

# separate the arguments passed to the different programs
for ARG in "$@"
do
	if [ "$ARG" == "--help" -o  "$ARG" == "-h" ] 
	then
		showUsage
		exit
	fi
	if [ "$ARG" == "--tspass" ]
	then
		TSPASS_ARG="true"
		continue
	fi
	if [ -z "$TSPASS_ARG" ]
	then
		TRANSLATE_ARGS="$TRANSLATE_ARGS $ARG"
	else
		if [ "$ARG" == "-ModelConstruction" ] || [ "$ARG" == "-ModelConstruction=1" ]
		then
			TRANSLATE_ARGS="$TRANSLATE_ARGS --singleeventuality"
		fi
		TSPASS_ARGS="$TSPASS_ARGS $ARG"
	fi
done

echo "Arguments for the \"fotl-translate\" tool: $TRANSLATE_ARGS"

echo "Arguments for TSPASS: $TSPASS_ARGS"

PATH=`dirname $0`:$PATH
fotl-translate $TRANSLATE_ARGS | tspass -Stdin $TSPASS_ARGS

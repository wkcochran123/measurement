for x in $(find device/Measurement | grep lean); do
	echo ------------------------------------------------
	echo ${x}
	echo ------------------------------------------------
    cat ${x}
done

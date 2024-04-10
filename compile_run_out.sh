cargo run -- out.ir
as -o out.o out.s
ld -o out out.o \
	-lSystem \
	-syslibroot `xcrun -sdk macosx --show-sdk-path` \
	-e _start \
	-arch arm64
./out
echo $?

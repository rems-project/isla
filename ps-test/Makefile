test-sub.sym:
	../target/release/isla-footprint -a aarch64.ir -i "sub sp, sp, #16" 2> /dev/null > test-sub.sym

# looks like branches aren't supported yet
test-branch-cond.sym:
	../target/release/isla-footprint -a aarch64.ir -i "b.ne 0x400168c4" 2> /dev/null > test-branch-cond.sym


aarch64.ir:
	$(MAKE) -C ../../sail-arm/arm-v8.5-a aarch64.ir
	cat ../../sail-arm/arm-v8.5-a/aarch64.ir footprint.ir > aarch64.ir

clean:
	rm -rf *~

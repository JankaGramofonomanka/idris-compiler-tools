declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)









define i32 @main() {
    entry:
        %r0 = sub i32 0, 1
        %r1 = call i32 @f(i32 1, i32 %r0)
        call void @printInt(i32 %r1)
        ret i32 0
}

define i32 @f(i32 %r3, i32 %r4) {
    entry:
        %r5 = icmp sgt i32 %r3, 0
        br i1 %r5, label %L3, label %L2
    L3:
        %r6 = icmp sgt i32 %r4, 0
        br i1 %r6, label %L0, label %L2
    L2:
        %r7 = icmp slt i32 %r3, 0
        br i1 %r7, label %L4, label %L1
    L4:
        %r8 = icmp slt i32 %r4, 0
        br i1 %r8, label %L0, label %L1
    L0:
        ret i32 7
    L1:
        ret i32 42
}

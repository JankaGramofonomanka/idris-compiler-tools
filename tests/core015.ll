declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)









define i32 @main() {
    entry:
        %r0 = call i32 @ev(i32 17)
        call void @printInt(i32 %r0)
        ret i32 0
}

define i32 @ev(i32 %r2) {
    entry:
        %r3 = icmp sgt i32 %r2, 0
        br i1 %r3, label %L0, label %L1
    L0:
        %r4 = sub i32 %r2, 2
        %r5 = call i32 @ev(i32 %r4)
        ret i32 %r5
    L1:
        %r6 = icmp slt i32 %r2, 0
        br i1 %r6, label %L2, label %L3
    L2:
        ret i32 0
    L3:
        ret i32 1
}

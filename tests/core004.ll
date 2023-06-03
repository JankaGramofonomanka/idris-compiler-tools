declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)









define i32 @main() {
    entry:
        %r0 = icmp eq i1 1, 1
        br i1 %r0, label %L1, label %L0
    L1:
        call void @printInt(i32 42)
        br label %L0
    L0:
        ret i32 0
}

declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)









define i32 @main() {
    entry:
        br i1 1, label %L1, label %L0
    L1:
        call void @printInt(i32 1)
        ret i32 0
    L0:
        ret i32 1
}

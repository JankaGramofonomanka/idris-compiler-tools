declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)









define i32 @main() {
    entry:
        call void @p()
        call void @printInt(i32 1)
        ret i32 0
}

define void @p() {
    entry:
        ret void
}

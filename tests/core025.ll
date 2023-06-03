declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)









define i32 @main() {
    entry:
        %r0 = sub i32 0, 2
        %r1 = mul i32 2, %r0
        call void @printInt(i32 %r1)
        ret i32 0
}

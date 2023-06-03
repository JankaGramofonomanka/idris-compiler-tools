declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)









define i32 @main() {
    entry:
        %r0 = sub i32 0, 42
        %r1 = sub i32 0, 1
        %r2 = sdiv i32 %r0, %r1
        call void @printInt(i32 %r2)
        ret i32 0
}

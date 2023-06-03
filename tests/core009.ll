declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)









define i32 @main() {
    entry:
        %r0 = call i32 @foo()
                                                                                                    ;x = foo()
                                                                                                    ;x ~ %r0
        call void @printInt(i32 %r0)
        ret i32 0
}

define i32 @foo() {
    entry:
        ret i32 10
}

declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)









define i32 @main() {
    entry:
                                                                                                    ;x = 0
                                                                                                    ;x ~ 0
                                                                                                    ;y = 7
                                                                                                    ;y ~ 7
        %r0 = sub i32 0, 1234234
                                                                                                    ;x = -(1234234)
                                                                                                    ;x ~ %r0
        call void @printInt(i32 %r0)
        call void @printInt(i32 7)
        ret i32 0
}

﻿// Copyright (c) Microsoft.  All Rights Reserved.  Licensed under the Apache License, Version 2.0.  See License.txt in the project root for license information.

#nullable enable

using Microsoft.CodeAnalysis.Debugging;

namespace Microsoft.CodeAnalysis.ExternalAccess.VSTypeScript.Api
{
    internal readonly struct VSTypeScriptDebugLocationInfoWrapper
    {
        internal readonly DebugLocationInfo UnderlyingObject;

        public VSTypeScriptDebugLocationInfoWrapper(string name, int lineOffset)
            => UnderlyingObject = new DebugLocationInfo(name, lineOffset);

        public readonly string Name => UnderlyingObject.Name;
        public readonly int LineOffset => UnderlyingObject.LineOffset;
        internal bool IsDefault => UnderlyingObject.IsDefault;
    }
}

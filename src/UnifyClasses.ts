"use strict";

import { Map, OrderedMap, OrderedSet } from "immutable";

import { Type, ClassProperty, UnionType, ObjectType } from "./Type";
import { assertIsObject } from "./TypeUtils";
import { TypeRef, TypeBuilder } from "./TypeBuilder";
import { TypeLookerUp, GraphRewriteBuilder } from "./GraphRewriting";
import { UnionBuilder, TypeRefUnionAccumulator } from "./UnionBuilder";
import { panic, assert, defined, MultiSet, toMultiSet, multiSetUnion, multiSetAdd } from "./Support";
import { TypeAttributes, combineTypeAttributes, emptyTypeAttributes } from "./TypeAttributes";

function getCliqueProperties(
    clique: ObjectType[],
    makePropertyType: (types: MultiSet<Type>) => TypeRef
): [OrderedMap<string, ClassProperty>, TypeRef | undefined, boolean] {
    let lostTypeAttributes = false;
    let propertyNames = OrderedSet<string>();
    for (const o of clique) {
        propertyNames = propertyNames.union(o.getProperties().keySeq());
    }

    let properties = propertyNames.toArray().map(name => [name, Map(), false] as [string, MultiSet<Type>, boolean]);
    let additionalProperties: MultiSet<Type> | undefined = undefined;
    for (const o of clique) {
        let additional = o.getAdditionalProperties();
        if (additional !== undefined) {
            if (additionalProperties === undefined) {
                additionalProperties = Map();
            }
            if (additional !== undefined) {
                additionalProperties = multiSetAdd(additionalProperties, additional);
            }
        }

        for (let i = 0; i < properties.length; i++) {
            let [name, types, isOptional] = properties[i];
            const maybeProperty = o.getProperties().get(name);
            if (maybeProperty === undefined) {
                isOptional = true;
                if (additional !== undefined && additional.kind !== "any") {
                    types = multiSetAdd(types, additional);
                }
            } else {
                if (maybeProperty.isOptional) {
                    isOptional = true;
                }
                types = multiSetAdd(types, maybeProperty.type);
            }

            properties[i][1] = types;
            properties[i][2] = isOptional;
        }
    }

    const unifiedAdditionalProperties =
        additionalProperties === undefined ? undefined : makePropertyType(additionalProperties);

    const unifiedPropertiesArray = properties.map(([name, types, isOptional]) => {
        return [name, new ClassProperty(makePropertyType(types), isOptional)] as [string, ClassProperty];
    });
    const unifiedProperties = OrderedMap(unifiedPropertiesArray);

    return [unifiedProperties, unifiedAdditionalProperties, lostTypeAttributes];
}

function countProperties(
    clique: ObjectType[]
): { hasProperties: boolean; hasAdditionalProperties: boolean; hasNonAnyAdditionalProperties: boolean } {
    let hasProperties = false;
    let hasAdditionalProperties = false;
    let hasNonAnyAdditionalProperties = false;
    for (const o of clique) {
        if (!o.getProperties().isEmpty()) {
            hasProperties = true;
        }
        const additional = o.getAdditionalProperties();
        if (additional !== undefined) {
            hasAdditionalProperties = true;
            if (additional.kind !== "any") {
                hasNonAnyAdditionalProperties = true;
            }
        }
    }
    return { hasProperties, hasAdditionalProperties, hasNonAnyAdditionalProperties };
}

export class UnifyUnionBuilder extends UnionBuilder<TypeBuilder & TypeLookerUp, TypeRef[], TypeRef[]> {
    constructor(
        typeBuilder: TypeBuilder & TypeLookerUp,
        private readonly _makeObjectTypes: boolean,
        private readonly _makeClassesFixed: boolean,
        private readonly _unifyTypes: (typesToUnify: MultiSet<TypeRef>) => TypeRef
    ) {
        super(typeBuilder);
    }

    protected makeObject(
        objectRefs: TypeRef[],
        typeAttributes: TypeAttributes,
        forwardingRef: TypeRef | undefined
    ): TypeRef {
        const maybeTypeRef = this.typeBuilder.lookupTypeRefs(objectRefs, forwardingRef);
        if (maybeTypeRef !== undefined) {
            assert(
                forwardingRef === undefined || maybeTypeRef === forwardingRef,
                "The forwarding ref must be consumed"
            );
            this.typeBuilder.addAttributes(maybeTypeRef, typeAttributes);
            return maybeTypeRef;
        }

        const objectTypes = objectRefs.map(r => assertIsObject(r.deref()[0]));
        const { hasProperties, hasAdditionalProperties, hasNonAnyAdditionalProperties } = countProperties(objectTypes);

        if (!this._makeObjectTypes && (hasNonAnyAdditionalProperties || (!hasProperties && hasAdditionalProperties))) {
            const propertyTypes = multiSetUnion(
                ...objectTypes.map(o => toMultiSet(o.getProperties().map(cp => cp.typeRef)))
            );
            const additionalPropertyTypes = OrderedSet(
                objectTypes
                    .filter(o => o.getAdditionalProperties() !== undefined)
                    .map(o => defined(o.getAdditionalProperties()).typeRef)
            );
            const allPropertyTypes = multiSetUnion(propertyTypes, toMultiSet(additionalPropertyTypes));
            const tref = this.typeBuilder.getMapType(this._unifyTypes(allPropertyTypes));
            this.typeBuilder.addAttributes(tref, typeAttributes);
            return tref;
        } else {
            const [properties, additionalProperties, lostTypeAttributes] = getCliqueProperties(objectTypes, types => {
                assert(types.size > 0, "Property has no type");
                return this._unifyTypes(types.mapKeys(t => t.typeRef));
            });
            if (lostTypeAttributes) {
                this.typeBuilder.setLostTypeAttributes();
            }
            if (this._makeObjectTypes) {
                return this.typeBuilder.getUniqueObjectType(
                    typeAttributes,
                    properties,
                    additionalProperties,
                    forwardingRef
                );
            } else {
                assert(additionalProperties === undefined, "We have additional properties but want to make a class");
                return this.typeBuilder.getUniqueClassType(
                    typeAttributes,
                    this._makeClassesFixed,
                    properties,
                    forwardingRef
                );
            }
        }
    }

    protected makeArray(
        arrays: TypeRef[],
        typeAttributes: TypeAttributes,
        forwardingRef: TypeRef | undefined
    ): TypeRef {
        const ref = this.typeBuilder.getArrayType(this._unifyTypes(toMultiSet(arrays)), forwardingRef);
        this.typeBuilder.addAttributes(ref, typeAttributes);
        return ref;
    }
}

export function unionBuilderForUnification<T extends Type>(
    typeBuilder: GraphRewriteBuilder<T>,
    makeObjectTypes: boolean,
    makeClassesFixed: boolean,
    conflateNumbers: boolean
): UnionBuilder<TypeBuilder & TypeLookerUp, TypeRef[], TypeRef[]> {
    return new UnifyUnionBuilder(typeBuilder, makeObjectTypes, makeClassesFixed, trefs =>
        unifyTypes(
            trefs.mapKeys(tref => tref.deref()[0]),
            emptyTypeAttributes,
            typeBuilder,
            unionBuilderForUnification(typeBuilder, makeObjectTypes, makeClassesFixed, conflateNumbers),
            conflateNumbers
        )
    );
}

function multiplyTypeAttributes(attributes: TypeAttributes, count: number): TypeAttributes {
    let result = attributes;
    count -= 1;
    while (count > 0) {
        if (count % 2 === 0) {
            result = combineTypeAttributes(result, result);
            count /= 2;
        } else {
            result = combineTypeAttributes(result, attributes);
            count -= 1;
        }
    }
    return result;
}

// FIXME: The UnionBuilder might end up not being used.
export function unifyTypes<T extends Type>(
    typeCounts: MultiSet<Type>,
    typeAttributes: TypeAttributes,
    typeBuilder: GraphRewriteBuilder<T>,
    unionBuilder: UnionBuilder<TypeBuilder & TypeLookerUp, TypeRef[], TypeRef[]>,
    conflateNumbers: boolean,
    maybeForwardingRef?: TypeRef
): TypeRef {
    const types = typeCounts.keySeq().toSet();
    if (types.isEmpty()) {
        return panic("Cannot unify empty set of types");
    } else if (types.count() === 1) {
        const first = defined(types.first());
        const count = defined(typeCounts.get(first));
        if (count > 1) {
            typeAttributes = combineTypeAttributes(
                typeAttributes,
                multiplyTypeAttributes(first.getAttributes(), count - 1)
            );
        }
        if (!(first instanceof UnionType)) {
            return typeBuilder.reconstituteTypeRef(first.typeRef, typeAttributes, maybeForwardingRef);
        }
    }

    const typeRefs = types.toArray().map(t => t.typeRef);
    const maybeTypeRef = typeBuilder.lookupTypeRefs(typeRefs, maybeForwardingRef);
    if (maybeTypeRef !== undefined) {
        typeBuilder.addAttributes(maybeTypeRef, typeAttributes);
        return maybeTypeRef;
    }

    const accumulator = new TypeRefUnionAccumulator(conflateNumbers);
    const nestedAttributes = accumulator.addTypes(types);
    typeAttributes = combineTypeAttributes(typeAttributes, nestedAttributes);

    return typeBuilder.withForwardingRef(maybeForwardingRef, forwardingRef => {
        typeBuilder.registerUnion(typeRefs, forwardingRef);
        return unionBuilder.buildUnion(accumulator, false, typeAttributes, forwardingRef);
    });
}

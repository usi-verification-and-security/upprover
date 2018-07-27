//
// Created by Martin Blicha on 27.07.18.
//

#ifndef PROJECT_PARTITION_REPRESENTATION_H
#define PROJECT_PARTITION_REPRESENTATION_H

enum class partition_representation : int{
    NONE = 0,
    STUB = 1,
    SUMMARY = 2,
    SSA = 4
};

inline partition_representation operator|(partition_representation lhs, partition_representation rhs)
{
    return static_cast<partition_representation>(
            static_cast<std::underlying_type<partition_representation>::type>(lhs) |
            static_cast<std::underlying_type<partition_representation>::type>(rhs));
}

inline partition_representation operator&(partition_representation lhs, partition_representation rhs)
{
    return static_cast<partition_representation>(
            static_cast<std::underlying_type<partition_representation>::type>(lhs) &
            static_cast<std::underlying_type<partition_representation>::type>(rhs));
}

inline partition_representation operator~(partition_representation v){
    return static_cast<partition_representation >(
            ~(static_cast<std::underlying_type<partition_representation >::type>(v))
    );
}

#endif //PROJECT_PARTITION_REPRESENTATION_H

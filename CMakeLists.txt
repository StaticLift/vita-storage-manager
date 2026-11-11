cmake_minimum_required(VERSION 3.16)

if(NOT DEFINED CMAKE_TOOLCHAIN_FILE)
  set(CMAKE_TOOLCHAIN_FILE "$ENV{VITASDK}/share/vita.toolchain.cmake" CACHE PATH "toolchain file")
endif()

project(storage C)
include("$ENV{VITASDK}/share/vita.cmake" REQUIRED)

set(VITA_APP_NAME "Storage Manager")
set(VITA_TITLEID  "STRG00001")
set(VITA_VERSION  "01.00")

set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -O2 -Wall -Wno-format-truncation")
option(DEBUG_LOG "Write a step-by-step debug log to ux0:data/Storage/debug.log" OFF)
if(DEBUG_LOG)
  add_compile_definitions(DEBUG_LOG)
endif()

add_executable(storage src/main.c)
target_link_libraries(storage
  vita2d freetype png jpeg bz2 z m
  SceDisplay_stub SceGxm_stub SceSysmodule_stub SceCtrl_stub
  ScePgf_stub ScePvf_stub SceCommonDialog_stub SceAppMgr_stub SceAppUtil_stub
  SceRtc_stub ScePower_stub ScePromoterUtil_stub)

target_link_options(storage PRIVATE "-Wl,-T,${CMAKE_SOURCE_DIR}/src/sce_gap.ld")

# UNSAFE: the app has to read other apps' folders under ux0:.
vita_create_self(eboot.bin storage UNSAFE)
vita_create_vpk(VitaStorageManager.vpk ${VITA_TITLEID} eboot.bin
  VERSION ${VITA_VERSION}
  NAME ${VITA_APP_NAME}
  FILE sce_sys/icon0.png sce_sys/icon0.png
       sce_sys/livearea/contents/bg.png sce_sys/livearea/contents/bg.png
       sce_sys/livearea/contents/startup.png sce_sys/livearea/contents/startup.png
       sce_sys/livearea/contents/template.xml sce_sys/livearea/contents/template.xml
       assets/logo.png logo.png)

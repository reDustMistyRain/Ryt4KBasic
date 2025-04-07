"use strict";
console.log("遊戲腳本開始執行...");

// =============================================================================
// DOM 元素獲取與檢查
// =============================================================================
const appContainer = document.getElementById('app-container');
const songSelectScreen = document.getElementById('song-select-screen');
const songListContainer = document.getElementById('song-list-container');
const resultScreen = document.getElementById('result-screen');
const introScreen = document.getElementById('intro-screen');
const introIllustration = document.getElementById('intro-illustration');
const introTitle = document.getElementById('intro-title');
const introArtist = document.getElementById('intro-artist');
const resultIllustration = document.getElementById('result-illustration');
const resultTitle = document.getElementById('result-title');
const resultArtist = document.getElementById('result-artist');
const canvas = document.getElementById('gameCanvas');
const ctx = canvas.getContext('2d');
const speedDisplay = document.getElementById('speed-display');
const increaseSpeedButton = document.getElementById('increase-speed');
const decreaseSpeedButton = document.getElementById('decrease-speed');

if (!canvas || !ctx || !appContainer || !songSelectScreen || !songListContainer || !resultScreen || !introScreen || !introIllustration || !introTitle || !introArtist || !resultIllustration || !resultTitle || !resultArtist || !speedDisplay || !increaseSpeedButton || !decreaseSpeedButton) {
    console.error("錯誤：無法找到必要的 HTML 元素！"); alert("頁面初始化錯誤！"); throw new Error("...");
}

// =============================================================================
// 遊戲狀態管理
// =============================================================================
let gameState = 'INITIALIZING';
let availableSongs = [];
let selectedSongData = null;

// =============================================================================
// 遊戲核心參數與設定
// =============================================================================
const LANE_COUNT = 4; let JUDGMENT_LINE_Y = 0; let PERSPECTIVE_STRENGTH = 0.8;
let TOP_TOTAL_WIDTH = 0; let TOP_OFFSET_X = 0; let BOTTOM_LANE_WIDTH = 0; let TOP_LANE_WIDTH = 0;
const START_DELAY_SECONDS = 0.1;
const BASE_NOTE_APPEAR_TIME_OFFSET = 2.0;
let speedMultiplier = 1.0;
let noteAppearTimeOffset = BASE_NOTE_APPEAR_TIME_OFFSET / speedMultiplier;
const MIN_SPEED_MULTIPLIER = 0.5;
const MAX_SPEED_MULTIPLIER = 5.0;
const SPEED_ADJUST_STEP = 0.25;
const NOTE_HEIGHT_RATIO = 0.03; let NOTE_HEIGHT = 20;
const NOTE_SPEED_EASING_POWER = 2.2; const LINEAR_MIX_FACTOR = 0.15;

// =============================================================================
// 字體設定
// =============================================================================
const FONT_FAMILY_CANVAS = "'IBM Plex Mono', monospace";

// =============================================================================
// 顏色定義
// =============================================================================
const COLOR_BACKGROUND = '#000000'; // Fallback background
const COLOR_LINES = '#FFFFFF'; const COLOR_LANE_SEPARATOR = '#CCCCCC';
const COLOR_JUDGMENT_LINE = '#FF0000'; const COLOR_KEY_PRESSED = '#FFFF00';
const COLOR_NOTE = '#CCFFFF';
const COLOR_PERFECT_PARTICLE = 'rgba(255, 215, 0,';
const COLOR_GREAT_PARTICLE = 'rgba(144, 238, 144,';
const COLOR_GOOD_PARTICLE = 'rgba(173, 216, 230,';
const COLOR_LANE_FLASH = 'rgba(255, 182, 193,';
const COLOR_RING_EFFECT = 'rgba(255, 255, 255,';

// =============================================================================
// 判定與計分系統 (*** 修改：100萬分制 ***)
// =============================================================================
const JUDGE_WINDOW_PERFECT = 0.100; const JUDGE_WINDOW_GREAT = 0.200; const JUDGE_WINDOW_GOOD = 0.300; const JUDGE_WINDOW_MISS = 0.400;
let lastJudgment = { text: '', time: 0, column: -1 }; const JUDGMENT_DISPLAY_DURATION = 0.5;
let score = 0; let combo = 0; let maxCombo = 0;
const MAX_SCORE = 1000000; // 總分上限
let totalNotesInChart = 0; // 當前譜面的總Note數
let baseScorePerPerfect = 0; // Perfect 的基礎分數 (浮點數)
// Removed SCORE_PERFECT, SCORE_GREAT, SCORE_GOOD constants
let judgmentCounts = { perfect: 0, great: 0, good: 0, miss: 0 };

// =============================================================================
// 按鍵與音訊狀態
// =============================================================================
const KEY_MAPPINGS = ['KeyD', 'KeyF', 'KeyJ', 'KeyK']; const keyStates = {'KeyD': false, 'KeyF': false, 'KeyJ': false, 'KeyK': false};
const AudioContext = window.AudioContext || window.webkitAudioContext; let audioContext; let audioBuffer = null; let audioSource = null;
let audioStartTime = 0; let currentSongTime = 0; let rawElapsedTime = -START_DELAY_SECONDS;
let isAudioLoading = false; let isAudioReady = false; let isPlaying = false; let gameLoopRunning = false;

// Keysound
let keysoundBuffer = null; let isKeysoundLoading = false; let isKeysoundReady = false;
const KEYSOUND_PATH = 'assets/beat.wav'; const KEYSOUND_VOLUME = 0.3;

// =============================================================================
// 譜面數據
// =============================================================================
let chartData = null; let loadedNotes = []; let globalOffsetSeconds = 0;
let isChartLoading = false; let isChartReady = false;

// =============================================================================
// 背景圖相關
// =============================================================================
let songBgImage = null; let isSongBgLoading = false; let isSongBgReady = false;
const BACKGROUND_BLUR_AMOUNT = 5; const BACKGROUND_DIM_ALPHA = 0.7;

// =============================================================================
// 特效相關
// =============================================================================
let activeHitEffects = []; // Particles
let activeLaneFlashes = []; // Lane flash
let activeRingEffects = []; // Expanding ring
// Particle params
const PARTICLE_COUNT_PERFECT = 12; const PARTICLE_COUNT_GREAT = 8; const PARTICLE_COUNT_GOOD = 5;
const PARTICLE_BASE_SPEED = 100; const PARTICLE_RANDOM_SPEED = 100;
const PARTICLE_BASE_SIZE = 40; const PARTICLE_RANDOM_SIZE = 10;
const PARTICLE_MIN_LIFETIME = 0.3; const PARTICLE_MAX_LIFETIME = 0.6;
const PARTICLE_ANGULAR_VELOCITY_RANGE = Math.PI * 2;
// Lane flash params
const LANE_FLASH_DURATION = 0.15;
// Ring effect params
const RING_EFFECT_DURATION = 0.3;
const RING_EFFECT_START_SCALE = 0.2;
const RING_EFFECT_END_SCALE = 1.5;
const RING_EFFECT_LINE_WIDTH = 3;

// =============================================================================
// 初始化與狀態重置
// =============================================================================
function initializeGameState() {
    loadedNotes.forEach(note => { note.isActive = false; note.y = 0; note.judged = false; note.judgment = ''; });
    score = 0; // 重置分數為 0
    combo = 0; maxCombo = 0;
    lastJudgment = { text: '', time: 0, column: -1 };
    judgmentCounts = { perfect: 0, great: 0, good: 0, miss: 0 };
    activeHitEffects = [];
    activeLaneFlashes = [];
    activeRingEffects = [];
    // Base score per perfect depends on chart, reset elsewhere (in loadChart)
    console.log("遊戲狀態已重置。");
}

// =============================================================================
// 輔助函式
// =============================================================================
function getInterpolatedX(boundaryIndex, y) { if (BOTTOM_LANE_WIDTH === undefined || TOP_LANE_WIDTH === undefined || TOP_OFFSET_X === undefined || canvas.height <= 0) return 0; const bottomX = boundaryIndex * BOTTOM_LANE_WIDTH; const topX = TOP_OFFSET_X + (boundaryIndex * TOP_LANE_WIDTH); const clampedY = Math.max(0, Math.min(canvas.height, y)); const ratio = canvas.height > 0 ? (clampedY / canvas.height) : 0; return topX + (bottomX - topX) * ratio; }
function resizeCanvas() { const displayWidth = window.innerWidth; const displayHeight = window.innerHeight; if (Math.abs(canvas.width - displayWidth) > 1 || Math.abs(canvas.height - displayHeight) > 1) { canvas.width = displayWidth; canvas.height = displayHeight; console.log(`Canvas resized to: ${canvas.width} x ${canvas.height}`); JUDGMENT_LINE_Y = canvas.height * 0.85; TOP_TOTAL_WIDTH = canvas.width * (1 - PERSPECTIVE_STRENGTH); TOP_OFFSET_X = (canvas.width - TOP_TOTAL_WIDTH) / 2; BOTTOM_LANE_WIDTH = canvas.width / LANE_COUNT; TOP_LANE_WIDTH = TOP_TOTAL_WIDTH / LANE_COUNT; NOTE_HEIGHT = Math.max(10, Math.round(canvas.height * NOTE_HEIGHT_RATIO)); console.log(`重新計算參數: 判定線 Y=${JUDGMENT_LINE_Y.toFixed(0)}, 音符高度=${NOTE_HEIGHT}`); if (!gameLoopRunning && ctx && gameState !== 'LOADING' && gameState !== 'INITIALIZING' && gameState !== 'SELECTING') { drawGameBackground(); } } }
function drawGameBackground() { if (!ctx) return; ctx.clearRect(0, 0, canvas.width, canvas.height); if (isSongBgReady && songBgImage) { ctx.filter = `blur(${BACKGROUND_BLUR_AMOUNT}px)`; const canvasAspect = canvas.width / canvas.height; const bgAspect = songBgImage.naturalWidth / songBgImage.naturalHeight; let drawWidth, drawHeight, offsetX = 0, offsetY = 0; if (bgAspect > canvasAspect) { drawHeight = canvas.height; drawWidth = drawHeight * bgAspect; offsetX = (canvas.width - drawWidth) / 2; } else { drawWidth = canvas.width; drawHeight = drawWidth / bgAspect; offsetY = (canvas.height - drawHeight) / 2; } ctx.drawImage(songBgImage, offsetX, offsetY, drawWidth, drawHeight); ctx.filter = 'none'; ctx.fillStyle = `rgba(0, 0, 0, ${BACKGROUND_DIM_ALPHA})`; ctx.fillRect(0, 0, canvas.width, canvas.height); } else { ctx.fillStyle = COLOR_BACKGROUND; ctx.fillRect(0, 0, canvas.width, canvas.height); if (!isSongBgLoading && !isSongBgReady && selectedSongData?.illustrationPath) { loadSongBackgroundImage(selectedSongData.illustrationPath); } } if (gameState === 'GAME' || gameState === 'PLAYING') { drawPerspectiveStaticElements(); } }

// =============================================================================
// UI 畫面管理與更新
// =============================================================================
function showScreen(screenId) { const overlayScreens = [songSelectScreen, resultScreen, introScreen]; let targetOverlayScreen = null; let previousState = gameState; console.log(`[showScreen] 嘗試切換到畫面: ${screenId}`); overlayScreens.forEach(screen => { screen.classList.add('hidden'); screen.classList.remove('visible'); }); if (screenId === 'GAME' || screenId === 'LOADING' || screenId === 'INITIALIZING') { if (screenId === 'GAME') { canvas.classList.remove('hidden'); console.log("[showScreen] Canvas 設為可見"); } else { canvas.classList.add('hidden'); console.log(`[showScreen] Canvas 設為隱藏 (狀態: ${screenId})`); } } else { canvas.classList.add('hidden'); console.log(`[showScreen] Canvas 設為隱藏 (狀態: ${screenId})`); } switch (screenId) { case 'SELECTING': targetOverlayScreen = songSelectScreen; if (isPlaying) { if (audioSource) { try { audioSource.stop(); } catch(e){} audioSource.disconnect(); } isPlaying = false; audioSource = null; } gameLoopRunning = false; isAudioReady = false; isChartReady = false; selectedSongData = null; chartData = null; audioBuffer = null; loadedNotes = []; activeHitEffects = []; activeLaneFlashes = []; activeRingEffects = []; songBgImage = null; isSongBgLoading = false; isSongBgReady = false; gameInfoIllustration = null; gameInfoIllustrationSrc = ''; // *** 清空遊戲內曲繪狀態 ***
 console.log("返回選曲並重置部分資源"); break; case 'RESULT': targetOverlayScreen = resultScreen; break; case 'INTRO': targetOverlayScreen = introScreen; break; case 'GAME': case 'LOADING': case 'INITIALIZING': targetOverlayScreen = null; break; default: console.error("未知的畫面 ID:", screenId); targetOverlayScreen = songSelectScreen; screenId = 'SELECTING'; break; } gameState = screenId; if (targetOverlayScreen) { targetOverlayScreen.classList.remove('hidden'); console.log(`[showScreen] ${targetOverlayScreen.id} 畫面已移除 hidden`); requestAnimationFrame(() => { setTimeout(() => { if (gameState === screenId) { targetOverlayScreen.classList.add('visible'); console.log(`[showScreen] ${targetOverlayScreen.id} (${screenId}) set to visible`); } else { console.log(`[showScreen] State changed (${gameState}) before ${targetOverlayScreen.id} (${screenId}) could become visible.`); } }, 50); }); } else { console.log(`[showScreen] ${screenId} 狀態，無特定疊加畫面。`); } console.log(`[showScreen] 狀態從 ${previousState} 切換到: ${gameState}`); if (screenId !== 'GAME' && !gameLoopRunning) { if (canvas.width === 0 || canvas.height === 0) resizeCanvas(); drawGameBackground(); } }
function populateSongList() { /* ... (no change) ... */ if (!songListContainer) return; songListContainer.innerHTML = ''; if (availableSongs.length === 0) { songListContainer.innerHTML = '<p>未找到歌曲。</p>'; return; } availableSongs.sort((a, b) => a.title.localeCompare(b.title)); availableSongs.forEach(song => { const songItem = document.createElement('div'); songItem.classList.add('song-item'); songItem.dataset.songId = song.id; songItem.dataset.chartPath = song.chartPath; songItem.dataset.audioPath = song.audioPath; songItem.dataset.illustrationPath = song.illustrationPath; songItem.dataset.title = song.title; songItem.dataset.artist = song.artist || '未知'; const img = document.createElement('img'); img.classList.add('song-illustration'); img.src = song.illustrationPath; img.alt = song.title; img.onerror = () => { img.src = 'placeholder.png'; }; const details = document.createElement('div'); details.classList.add('song-details'); const titleP = document.createElement('p'); titleP.classList.add('song-title'); titleP.textContent = song.title; const artistP = document.createElement('p'); artistP.classList.add('song-artist'); artistP.textContent = song.artist || '未知'; details.appendChild(titleP); details.appendChild(artistP); songItem.appendChild(img); songItem.appendChild(details); songItem.addEventListener('click', handleSongSelect); songListContainer.appendChild(songItem); }); }

// =============================================================================
// 資源載入與狀態檢查
// =============================================================================
async function loadAudio(url) { /* ... (no change) ... */ if (!audioContext || isAudioLoading || isAudioReady || !url) return; isAudioLoading = true; updateLoadingStatus(); console.log(`載入音訊: ${url}...`); try { const response = await fetch(url); if (!response.ok) throw new Error(`HTTP error! status: ${response.status}`); const arrayBuffer = await response.arrayBuffer(); audioBuffer = await audioContext.decodeAudioData(arrayBuffer); isAudioReady = true; console.log("歌曲音訊載入完成！"); checkAndTriggerIntro(); } catch (error) { console.error(`載入音訊錯誤 (${url}):`, error); alert(`載入歌曲音訊失敗: ${url}\n${error.message}`); showScreen('SELECTING'); audioBuffer = null; isAudioReady = false; } finally { isAudioLoading = false; updateLoadingStatus(); } }
async function loadChart(url) { // *** 修改：計算基礎分數 ***
    if (isChartLoading || isChartReady || !url) return;
    isChartLoading = true;
    updateLoadingStatus();
    console.log(`載入譜面: ${url}...`);
    try {
        const response = await fetch(url);
        if (!response.ok) throw new Error(`無法載入譜面: ${response.statusText}`);
        chartData = await response.json();
        if (!chartData || !chartData.notes || !chartData.metadata) throw new Error("譜面格式錯誤");
        globalOffsetSeconds = (chartData.metadata.global_offset_ms || 0) / 1000.0;
        loadedNotes = [];
        chartData.notes.forEach(note => { if (note.targetTime !== undefined && note.column !== undefined) { const adjustedTargetTime = note.targetTime + globalOffsetSeconds; loadedNotes.push({ ...note, originalTargetTime: note.targetTime, targetTime: adjustedTargetTime, isActive: false, y: 0, judged: false, judgment: '' }); } else { console.warn("忽略格式不符音符:", note); } });

        // *** 計算分數 ***
        totalNotesInChart = loadedNotes.length;
        if (totalNotesInChart > 0) {
            baseScorePerPerfect = MAX_SCORE / totalNotesInChart;
            console.log(`譜面載入完成！共 ${totalNotesInChart} 音符。Perfect基礎分數: ${baseScorePerPerfect.toFixed(4)}`);
        } else {
            baseScorePerPerfect = 0; // Avoid division by zero
            console.warn("譜面載入完成，但 Note 數量為 0！");
        }

        isChartReady = true;
        checkAndTriggerIntro();
    } catch (error) {
        console.error(`載入譜面錯誤 (${url}):`, error);
        alert(`載入譜面失敗: ${url}\n${error.message}`);
        showScreen('SELECTING');
        chartData = null; loadedNotes = []; totalNotesInChart = 0; baseScorePerPerfect = 0; isChartReady = false;
    } finally {
        isChartLoading = false;
        updateLoadingStatus();
    }
}
async function loadKeysound() { /* ... (no change) ... */ if (!audioContext || isKeysoundLoading || isKeysoundReady) return; isKeysoundLoading = true; console.log(`載入打擊音效: ${KEYSOUND_PATH}...`); try { const response = await fetch(KEYSOUND_PATH); if (!response.ok) throw new Error(`HTTP error! status: ${response.status}`); const arrayBuffer = await response.arrayBuffer(); keysoundBuffer = await audioContext.decodeAudioData(arrayBuffer); isKeysoundReady = true; console.log("打擊音效載入完成！"); } catch (error) { console.error("載入打擊音效錯誤:", error); keysoundBuffer = null; isKeysoundReady = false; } finally { isKeysoundLoading = false; } }
async function loadSongBackgroundImage(url) { if (!url) { console.warn("歌曲無背景圖路徑，使用預設背景。"); songBgImage = null; isSongBgReady = false; isSongBgLoading = false; return; } if (songBgImage && songBgImage.src.endsWith(url.split('/').pop())) { console.log("歌曲背景圖似乎已載入，跳過。"); isSongBgReady = true; isSongBgLoading = false; return; } isSongBgLoading = true; isSongBgReady = false; songBgImage = null; console.log(`載入歌曲背景圖: ${url}...`); updateLoadingStatus(); try { const img = new Image(); await new Promise((resolve, reject) => { img.onload = () => { songBgImage = img; isSongBgReady = true; console.log("歌曲背景圖載入完成！"); resolve(); }; img.onerror = (err) => { console.error(`載入歌曲背景圖錯誤 (${url}):`, err); songBgImage = null; isSongBgReady = false; reject(err); }; img.src = url; }); } catch (error) { /* Error logged in onerror */ } finally { isSongBgLoading = false; updateLoadingStatus(); } }
function updateLoadingStatus() { /* ... (no change) ... */ if (gameState === 'LOADING') { console.log(`載入狀態: SongBG ${isSongBgLoading?'中':(isSongBgReady?'完成':'失敗/未載入')}, 音訊 ${isAudioLoading ? '中' : (isAudioReady ? '完成' : '失敗/未載入')}, 譜面 ${isChartLoading ? '中' : (isChartReady ? '完成' : '失敗/未載入')}, Keysound ${isKeysoundLoading ? '中' : (isKeysoundReady ? '完成' : '失敗/未載入')}`); } }
function checkAndTriggerIntro() { /* ... (no change) ... */ if (isAudioReady && isChartReady && gameState === 'LOADING') { console.log("音訊和譜面均已就緒，觸發 Intro..."); startIntro(); } else { console.log("等待資源中...", {isAudioReady, isChartReady, gameState}); } }

// =============================================================================
// Intro 畫面處理
// =============================================================================
function showIntroScreen() { /* ... (no change) ... */ if (!selectedSongData) { console.error("無法顯示 Intro，未選歌！"); showScreen('SELECTING'); return; } introIllustration.src = selectedSongData.illustrationPath || 'placeholder.png'; introIllustration.onerror = () => { introIllustration.src = 'placeholder.png'; }; introTitle.textContent = selectedSongData.title || '未知歌曲'; introArtist.textContent = selectedSongData.artist || '未知作曲家'; showScreen('INTRO'); console.log("Intro 顯示，3 秒後自動開始遊戲..."); setTimeout(() => { if (gameState === 'INTRO') { console.log("Intro 時間到，開始淡出..."); introScreen.classList.remove('visible'); setTimeout(() => { if (gameState === 'INTRO' || gameState === 'PLAYING' || gameState === 'GAME') { console.log("Intro 淡出完成，開始播放..."); playAudio(); } else { console.log("Intro 淡出定時器完成，但狀態已變，不播放音樂。"); } }, 500); } else { console.log("Intro 主定時器觸發，但狀態已變，不執行淡出或播放。"); } }, 3000); }
const startIntro = showIntroScreen;

// =============================================================================
// 音訊播放與遊戲流程控制
// =============================================================================
function playKeysound() { /* ... (no change) ... */ if (isKeysoundReady && keysoundBuffer && audioContext && audioContext.state === 'running') { try { const source = audioContext.createBufferSource(); source.buffer = keysoundBuffer; const gainNode = audioContext.createGain(); gainNode.gain.value = KEYSOUND_VOLUME; source.connect(gainNode); gainNode.connect(audioContext.destination); source.start(0); } catch (error) { console.error("播放打擊音效失敗:", error); } } }
function playAudio() { /* ... (no change) ... */ if (isPlaying || !audioContext || !audioBuffer || !chartData) { console.warn("無法播放歌曲，狀態或資源異常。", {isPlaying, audioContext, audioBufferExists: !!audioBuffer, chartDataExists: !!chartData }); return; } showScreen('GAME'); if (audioSource) { try { audioSource.stop(); } catch(e) { console.warn("停止舊音源時出錯(可能已停止):", e); } audioSource.disconnect(); audioSource = null; } audioSource = audioContext.createBufferSource(); audioSource.buffer = audioBuffer; audioSource.connect(audioContext.destination); const scheduledStartTime = audioContext.currentTime + START_DELAY_SECONDS; audioStartTime = scheduledStartTime; isPlaying = true; rawElapsedTime = -START_DELAY_SECONDS; currentSongTime = 0; console.log(`音樂預計開始於 AC 時間: ${audioStartTime.toFixed(3)}`); initializeGameState(); audioSource.start(scheduledStartTime, 0); audioSource.onended = () => { console.log("音樂播放結束事件觸發。"); const wasPlaying = isPlaying; isPlaying = false; audioSource = null; if (wasPlaying && (gameState === 'PLAYING' || gameState === 'GAME')) { console.log("音樂自然結束，顯示結算畫面。"); showResultScreen(); } else { console.log(`音樂結束，但狀態為 ${gameState} 或非自然停止 (wasPlaying: ${wasPlaying})，不顯示結算。`); } }; if (!gameLoopRunning) { console.log("遊戲迴圈啟動..."); gameLoopRunning = true; requestAnimationFrame(gameLoop); } else { console.warn("playAudio 被調用，但 gameLoopRunning 已經是 true？") } }
function startGame(songData) { /* ... (no change) ... */ if (!songData || !songData.audioPath || !songData.chartPath) { console.error("無效歌曲數據！無法開始遊戲。"); alert("選擇的歌曲資料不完整！"); showScreen('SELECTING'); return; } selectedSongData = songData; console.log(`選中歌曲: ${selectedSongData.title}`); isAudioReady = false; isChartReady = false; audioBuffer = null; chartData = null; loadedNotes = []; activeHitEffects = []; activeLaneFlashes = []; activeRingEffects = []; isSongBgReady = false; isSongBgLoading = false; songBgImage = null; gameInfoIllustration = null; gameInfoIllustrationSrc = ''; showScreen('LOADING'); initializeAudioContextAndLoad(); }
function initializeAudioContextAndLoad() { /* ... (no change) ... */ if (!audioContext) { try { audioContext = new AudioContext(); console.log("AC 初始化成功。"); } catch (e) { console.error("無法創建 AC:", e); alert("無法初始化音訊系統。請檢查瀏覽器支援或設定。"); showScreen('SELECTING'); return; } } const loadResources = async () => { console.log("AC 狀態:", audioContext.state, "準備載入資源..."); updateLoadingStatus(); const loadPromises = []; if (selectedSongData?.illustrationPath) { loadPromises.push(loadSongBackgroundImage(selectedSongData.illustrationPath)); } else { console.warn("未提供歌曲背景圖路徑。"); isSongBgReady = false; isSongBgLoading = false; songBgImage = null; } if (!isKeysoundReady && !isKeysoundLoading) { loadPromises.push(loadKeysound()); } if (selectedSongData.audioPath) { loadPromises.push(loadAudio(selectedSongData.audioPath)); } else { console.error("歌曲音訊路徑無效！"); alert("錯誤：歌曲缺少音訊檔案路徑！"); showScreen('SELECTING'); return; } if (selectedSongData.chartPath) { loadPromises.push(loadChart(selectedSongData.chartPath)); } else { console.error("歌曲譜面路徑無效！"); alert("錯誤：歌曲缺少譜面檔案路徑！"); showScreen('SELECTING'); return; } try { await Promise.all(loadPromises); console.log("所有主要資源載入 Promise 完成。"); } catch (error) { console.error("資源載入過程中出現未捕獲的錯誤 (Promise.all):", error); showScreen('SELECTING'); } finally { updateLoadingStatus(); } }; if (audioContext.state === 'suspended') { console.warn("AC 處於 suspended 狀態，嘗試恢復..."); audioContext.resume().then(() => { console.log("AC 已成功恢復！"); loadResources(); }).catch(err => { console.error("恢復 AC 失敗:", err); alert("無法啟用音訊。請嘗試與頁面互動（點擊/按鍵）或檢查瀏覽器設定。"); showScreen('SELECTING'); }); } else if (audioContext.state === 'running') { console.log("AC 已在運行中，直接載入資源。"); loadResources(); } else { console.error("AC 處於意外狀態:", audioContext.state); alert(`音訊系統狀態異常 (${audioContext.state})，無法載入歌曲。`); showScreen('SELECTING'); } }
function showResultScreen() { // *** 修改：處理 All Perfect 100萬分 ***
    gameLoopRunning = false; isPlaying = false; if (audioSource) { try { audioSource.stop(); } catch(e) {} audioSource.disconnect(); audioSource = null; }

    // *** All Perfect 檢查與修正 ***
    let finalScore = score;
    if (totalNotesInChart > 0 && judgmentCounts.perfect === totalNotesInChart && judgmentCounts.great === 0 && judgmentCounts.good === 0 && judgmentCounts.miss === 0) {
        console.log("檢測到 All Perfect! 強制設定分數為 1,000,000。");
        finalScore = MAX_SCORE;
    }

    const resultSongTitle = document.getElementById('result-title'); const resultArtist = document.getElementById('result-artist'); const resultIllustrationImg = document.getElementById('result-illustration'); const resultScore = document.getElementById('result-score'); const resultMaxCombo = document.getElementById('result-max-combo'); const resultPerfect = document.getElementById('result-perfect'); const resultGreat = document.getElementById('result-great'); const resultGood = document.getElementById('result-good'); const resultMiss = document.getElementById('result-miss'); const backButton = document.getElementById('back-to-select-button'); if (!resultScreen || !resultSongTitle || !resultArtist || !resultIllustrationImg || !resultScore || !resultMaxCombo || !resultPerfect || !resultGreat || !resultGood || !resultMiss || !backButton) { console.error("找不到結算畫面元素！"); showScreen('SELECTING'); return; }
    resultSongTitle.textContent = selectedSongData ? selectedSongData.title : '未知'; resultArtist.textContent = selectedSongData ? selectedSongData.artist : '未知'; resultIllustrationImg.src = selectedSongData ? selectedSongData.illustrationPath : 'placeholder.png'; resultIllustrationImg.onerror = () => { resultIllustrationImg.src = 'placeholder.png'; };
    // *** 顯示最終分數 (取整) ***
    resultScore.textContent = Math.round(finalScore).toString().padStart(7, '0');
    resultMaxCombo.textContent = maxCombo; resultPerfect.textContent = judgmentCounts.perfect; resultGreat.textContent = judgmentCounts.great; resultGood.textContent = judgmentCounts.good; resultMiss.textContent = judgmentCounts.miss;
    const newBackButton = backButton.cloneNode(true); if (backButton.parentNode) {backButton.parentNode.replaceChild(newBackButton, backButton);} else { console.warn("Could not replace back button, parent node not found");} newBackButton.addEventListener('click', handleBackToSelectClick);
    showScreen('RESULT');
    console.log("顯示結算畫面");
}

// =============================================================================
// 繪圖函式 (Drawing Functions)
// =============================================================================
function drawPerspectiveStaticElements() { /* ... (no change) ... */ if (!ctx) return; const originalLineWidth = ctx.lineWidth; ctx.strokeStyle = COLOR_LANE_SEPARATOR; ctx.lineWidth = 1; for (let i = 1; i < LANE_COUNT; i++) { const topX = getInterpolatedX(i, 0); const bottomX = getInterpolatedX(i, canvas.height); ctx.beginPath(); ctx.moveTo(topX, 0); ctx.lineTo(bottomX, canvas.height); ctx.stroke(); } ctx.strokeStyle = COLOR_LINES; ctx.lineWidth = 6; ctx.beginPath(); ctx.moveTo(getInterpolatedX(0, 0), 0); ctx.lineTo(getInterpolatedX(0, canvas.height), canvas.height); ctx.stroke(); ctx.beginPath(); ctx.moveTo(getInterpolatedX(LANE_COUNT, 0), 0); ctx.lineTo(getInterpolatedX(LANE_COUNT, canvas.height), canvas.height); ctx.stroke(); ctx.strokeStyle = COLOR_JUDGMENT_LINE; ctx.lineWidth = 3; const judgmentLeftX = getInterpolatedX(0, JUDGMENT_LINE_Y); const judgmentRightX = getInterpolatedX(LANE_COUNT, JUDGMENT_LINE_Y); ctx.beginPath(); ctx.moveTo(judgmentLeftX, JUDGMENT_LINE_Y); ctx.lineTo(judgmentRightX, JUDGMENT_LINE_Y); ctx.stroke(); ctx.lineWidth = originalLineWidth; }
function drawNotes() { /* ... (no change) ... */ if (!ctx || !loadedNotes) return; ctx.fillStyle = COLOR_NOTE; loadedNotes.forEach(note => { if (!note.judged && note.isActive) { const topY = note.y; const judgmentLeftX = getInterpolatedX(note.column, JUDGMENT_LINE_Y); const judgmentRightX = getInterpolatedX(note.column + 1, JUDGMENT_LINE_Y); const widthAtJudgment = judgmentRightX - judgmentLeftX; const topLeftX = getInterpolatedX(note.column, topY); const topRightX = getInterpolatedX(note.column + 1, topY); const widthAtTop = topRightX - topLeftX; const heightScale = (widthAtJudgment > 0) ? (widthAtTop / widthAtJudgment) : 1; const minHeightScale = 0.1; const clampedHeightScale = Math.max(minHeightScale, heightScale); const currentVisualHeight = NOTE_HEIGHT * clampedHeightScale; const bottomY = topY + currentVisualHeight; if (topY < canvas.height && bottomY > 0) { const bottomLeftX = getInterpolatedX(note.column, bottomY); const bottomRightX = getInterpolatedX(note.column + 1, bottomY); ctx.beginPath(); ctx.moveTo(topLeftX, topY); ctx.lineTo(topRightX, topY); ctx.lineTo(bottomRightX, bottomY); ctx.lineTo(bottomLeftX, bottomY); ctx.closePath(); ctx.fill(); } } }); }
function drawJudgmentFeedback() { /* ... (no change) ... */ if (!ctx) return; if (lastJudgment.text && currentSongTime >= 0 && currentSongTime < lastJudgment.time + JUDGMENT_DISPLAY_DURATION) { const timeSinceJudgment = currentSongTime - lastJudgment.time; const alpha = 1.0 - (timeSinceJudgment / JUDGMENT_DISPLAY_DURATION); ctx.font = `bold 56px ${FONT_FAMILY_CANVAS}`; ctx.textAlign = 'center'; let judgmentColor = 'rgba(255, 255, 255, '; if (lastJudgment.text === 'Perfect') judgmentColor = COLOR_PERFECT_PARTICLE; else if (lastJudgment.text === 'Great') judgmentColor = COLOR_GREAT_PARTICLE; else if (lastJudgment.text === 'Good') judgmentColor = COLOR_GOOD_PARTICLE; else if (lastJudgment.text === 'Miss') judgmentColor = 'rgba(255, 0, 0, '; ctx.fillStyle = judgmentColor + Math.max(0, alpha) + ')'; const centerX = canvas.width / 2; const feedbackY = JUDGMENT_LINE_Y - 80; ctx.fillText(lastJudgment.text, centerX, feedbackY); } }
function drawScoreAndCombo() { // *** 修改：顯示取整後的分數 ***
    if (!ctx) return;
    // Score
    ctx.fillStyle = '#FFFFFF';
    ctx.font = `bold 32px ${FONT_FAMILY_CANVAS}`;
    ctx.textAlign = 'right';
    // Display rounded score during gameplay for better readability
    ctx.fillText(Math.round(score).toString().padStart(7, '0'), canvas.width - 20, 40);

    // Combo (no change needed for combo display itself)
    if (combo > 0) { ctx.font = `bold 64px ${FONT_FAMILY_CANVAS}`; ctx.textAlign = 'center'; const comboX = canvas.width / 2; const comboY = JUDGMENT_LINE_Y - 200; ctx.fillStyle = '#FFFF00'; ctx.fillText(combo, comboX, comboY); if (combo > 1) { ctx.font = `bold 32px ${FONT_FAMILY_CANVAS}`; ctx.fillStyle = '#FFFFFF'; ctx.fillText('Combos', comboX, comboY + 45); } }
    // Max Combo
    ctx.font = `bold 20px ${FONT_FAMILY_CANVAS}`; ctx.fillStyle = '#CCCCCC'; ctx.textAlign = 'right'; ctx.fillText(`Max Combo: ${maxCombo}`, canvas.width - 20, 70);
}
// *** 修改：修正遊戲內曲繪的繪製邏輯 ***
let gameInfoIllustration = null;
let gameInfoIllustrationSrc = ''; // Keep track of the *intended* source
let gameInfoIllustrationLoaded = false; // Track if the image object finished loading

function preloadGameInfoIllustration(src) {
    // Only start loading if the src is new and valid
    if (!src || src === gameInfoIllustrationSrc) {
        // If src is the same, check if it finished loading last time
        if (src === gameInfoIllustration?.src && gameInfoIllustration.complete) {
             gameInfoIllustrationLoaded = true; // Mark as loaded if already complete
        }
        return;
    }
    console.log("準備預載新的遊戲內曲繪:", src);
    gameInfoIllustrationSrc = src; // Set the intended source
    gameInfoIllustrationLoaded = false; // Mark as not loaded yet
    gameInfoIllustration = new Image(); // Create a new image object

    gameInfoIllustration.onload = () => {
        console.log("遊戲內曲繪載入完成:", src);
        // Crucial check: Only mark loaded if the source still matches the intended one
        // (Prevents marking loaded if user switched songs very quickly)
        if (gameInfoIllustrationSrc === src) {
            gameInfoIllustrationLoaded = true;
        } else {
             console.log("遊戲內曲繪載入完成，但目標已改變。");
        }
    };
    gameInfoIllustration.onerror = () => {
        console.warn("遊戲內曲繪失敗:", src);
        if (gameInfoIllustrationSrc === src) { // Only nullify if error is for the current intended src
             gameInfoIllustration = null;
             gameInfoIllustrationSrc = ''; // Reset src if loading fails
        }
         gameInfoIllustrationLoaded = false; // Ensure not marked loaded on error
    };
    gameInfoIllustration.src = src; // Start loading
}

function drawGameInfo() { // *** 修改：修正繪製邏輯 ***
    if (!ctx || !selectedSongData) return;
    const margin = 20; const imageSize = 50; const textSpacing = 8; const titleFontSize = 20; const artistFontSize = 14;

    // 1. Ensure the correct illustration is targeted for preload/check
    const currentIllustrationPath = selectedSongData.illustrationPath || '';
    if (currentIllustrationPath && gameInfoIllustrationSrc !== currentIllustrationPath) {
        preloadGameInfoIllustration(currentIllustrationPath); // Start loading if src mismatch
    }

    // 2. Draw the illustration ONLY if:
    //    - We have an image object (gameInfoIllustration)
    //    - It has finished loading (gameInfoIllustrationLoaded)
    //    - Its source matches the currently selected song's path
    if (gameInfoIllustration && gameInfoIllustrationLoaded && gameInfoIllustrationSrc === currentIllustrationPath) {
        ctx.globalAlpha = 0.8;
        ctx.drawImage(gameInfoIllustration, margin, margin, imageSize, imageSize);
        ctx.globalAlpha = 1.0;
    } else {
        // Optional: Draw a placeholder if needed while loading or if no image
        // ctx.fillStyle = 'rgba(255, 255, 255, 0.1)';
        // ctx.fillRect(margin, margin, imageSize, imageSize);
    }

    // 3. Draw text info (always drawn)
    ctx.fillStyle = 'rgba(255, 255, 255, 0.9)'; ctx.textAlign = 'left'; ctx.textBaseline = 'top';
    ctx.font = `bold ${titleFontSize}px ${FONT_FAMILY_CANVAS}`;
    ctx.fillText(selectedSongData.title || '未知', margin + imageSize + textSpacing, margin + 5);
    ctx.font = `${artistFontSize}px ${FONT_FAMILY_CANVAS}`;
    ctx.fillStyle = 'rgba(204, 204, 204, 0.9)';
    ctx.fillText(selectedSongData.artist || '未知', margin + imageSize + textSpacing, margin + titleFontSize + 8);
    ctx.textBaseline = 'alphabetic';
}


// =============================================================================
// 特效更新與繪製函數
// =============================================================================
function updateAndDrawHitEffects(currentTime) { /* ... (particle logic - no change) ... */ if (!ctx) return; activeHitEffects = activeHitEffects.filter(effect => { effect.particles = effect.particles.filter(particle => currentTime - particle.startTime < particle.lifetime); return effect.particles.length > 0; }); activeHitEffects.forEach(effect => { effect.particles.forEach(particle => { const elapsedTime = currentTime - particle.startTime; const lifetimeRatio = elapsedTime / particle.lifetime; particle.x += particle.vx * (1/60); particle.y += particle.vy * (1/60); particle.rotation += particle.angularVelocity * (1/60); particle.alpha = Math.max(0, 1.0 - lifetimeRatio); ctx.save(); ctx.fillStyle = particle.color + particle.alpha + ')'; ctx.globalAlpha = particle.alpha; ctx.translate(particle.x, particle.y); ctx.rotate(particle.rotation); const side = particle.size; const height = side * Math.sqrt(3) / 2; ctx.beginPath(); ctx.moveTo(0, -height / 2); ctx.lineTo(-side / 2, height / 2); ctx.lineTo(side / 2, height / 2); ctx.closePath(); ctx.fill(); ctx.restore(); }); }); ctx.globalAlpha = 1.0; }
function updateAndDrawLaneFlashes(currentTime) { /* ... (lane flash logic - no change) ... */ if (!ctx) return; activeLaneFlashes = activeLaneFlashes.filter(flash => currentTime - flash.startTime < flash.duration); activeLaneFlashes.forEach(flash => { const elapsedTime = currentTime - flash.startTime; const alpha = Math.max(0, 1.0 - (elapsedTime / flash.duration)); const laneIndex = flash.laneIndex; const bottomX1 = getInterpolatedX(laneIndex, JUDGMENT_LINE_Y); const bottomX2 = getInterpolatedX(laneIndex + 1, JUDGMENT_LINE_Y); const topX1 = getInterpolatedX(laneIndex, 0); const topX2 = getInterpolatedX(laneIndex + 1, 0); const gradient = ctx.createLinearGradient(0, JUDGMENT_LINE_Y, 0, 0); gradient.addColorStop(0, COLOR_LANE_FLASH + alpha + ')'); gradient.addColorStop(1, COLOR_LANE_FLASH + '0)'); ctx.fillStyle = gradient; ctx.beginPath(); ctx.moveTo(topX1, 0); ctx.lineTo(topX2, 0); ctx.lineTo(bottomX2, JUDGMENT_LINE_Y); ctx.lineTo(bottomX1, JUDGMENT_LINE_Y); ctx.closePath(); ctx.fill(); }); }
function updateAndDrawRingEffects(currentTime) { /* ... (ring effect logic - no change) ... */ if (!ctx) return; activeRingEffects = activeRingEffects.filter(ring => currentTime - ring.startTime < ring.duration); activeRingEffects.forEach(ring => { const elapsedTime = currentTime - ring.startTime; const progress = elapsedTime / ring.duration; const currentScale = RING_EFFECT_START_SCALE + (RING_EFFECT_END_SCALE - RING_EFFECT_START_SCALE) * progress; const currentAlpha = 1.0 - progress; const currentWidth = ring.startWidth * currentScale; const currentHeight = (ring.startWidth / 2) * currentScale; ctx.save(); ctx.globalAlpha = Math.max(0, currentAlpha); ctx.strokeStyle = COLOR_RING_EFFECT + Math.max(0, currentAlpha) + ')'; ctx.lineWidth = RING_EFFECT_LINE_WIDTH; ctx.beginPath(); ctx.ellipse( ring.centerX, ring.centerY, currentWidth / 2, currentHeight / 2, 0, 0, 2 * Math.PI ); ctx.stroke(); ctx.restore(); }); ctx.globalAlpha = 1.0; }

// =============================================================================
// 遊戲主迴圈 (Game Loop)
// =============================================================================
function gameLoop() {
    if (!gameLoopRunning) { console.log("遊戲迴圈已標記停止。"); return; }
    if (!isPlaying) { console.log("偵測到 isPlaying 為 false，停止遊戲迴圈。"); gameLoopRunning = false; if (gameState === 'PLAYING' || gameState === 'GAME') { console.warn("遊戲迴圈檢測到 isPlaying 為 false，但狀態仍是 GAME/PLAYING，嘗試顯示結果。"); } return; }
    if (audioContext && isPlaying && audioSource) { rawElapsedTime = audioContext.currentTime - audioStartTime; currentSongTime = Math.max(0, rawElapsedTime); } else { console.error("遊戲狀態異常：isPlaying 為 true 但 AudioContext 或 AudioSource 丟失！"); gameLoopRunning = false; showScreen('SELECTING'); return; }
    if (!ctx) { console.error("Canvas context lost!"); gameLoopRunning = false; return; }

    // 1. Draw Background (Blurred/Dimmed Song BG or Fallback)
    drawGameBackground();

    // 2. Update Notes state
    if (isPlaying) { loadedNotes.forEach(note => { if (!note.judged) { const appearTime = note.targetTime - noteAppearTimeOffset; if (rawElapsedTime >= appearTime) { note.isActive = true; const timeSinceAppearRaw = rawElapsedTime - appearTime; const timeProgressRaw = noteAppearTimeOffset > 0 ? Math.max(0, timeSinceAppearRaw / noteAppearTimeOffset) : 1; const yProgress = LINEAR_MIX_FACTOR * timeProgressRaw + (1 - LINEAR_MIX_FACTOR) * Math.pow(timeProgressRaw, NOTE_SPEED_EASING_POWER); note.y = yProgress * JUDGMENT_LINE_Y; if (currentSongTime > note.targetTime + JUDGE_WINDOW_MISS) { if (!note.judged) { console.log(`判定: Miss (超時) ID: ${note.id}`); note.judged = true; note.judgment = 'Miss'; note.isActive = false; lastJudgment = { text: 'Miss', time: currentSongTime, column: note.column }; combo = 0; judgmentCounts.miss++; } } } else { note.isActive = false; note.y = 0; } } else { note.isActive = false; } }); }

    // --- Draw Gameplay Elements in Order ---
    // 3. Lane Flashes (Behind Notes)
    updateAndDrawLaneFlashes(currentSongTime);
    // 4. Active Notes
    drawNotes();
    // 5. Ring Effects (On top of Notes at judgment line)
    updateAndDrawRingEffects(currentSongTime);
    // 6. Particle Effects (On top of Ring)
    updateAndDrawHitEffects(currentSongTime);
    // 7. Judgment Text (Highest layer for feedback)
    drawJudgmentFeedback();
    // 8. Score and Combo UI
    drawScoreAndCombo();
    // 9. Game Info UI (Top Left)
    drawGameInfo();

    // 10. Request Next Frame
    if (gameLoopRunning) { requestAnimationFrame(gameLoop); } else { console.log("gameLoopRunning 為 false，不請求下一幀。"); }
}

// =============================================================================
// 事件監聽器設定
// =============================================================================
window.addEventListener('keydown', function(event) { // *** 修改：使用新的計分邏輯 ***
    if (KEY_MAPPINGS.includes(event.code) || event.code === 'Escape') { /* event.preventDefault(); */ }
    const keyCode = event.code;
    if (keyCode === 'Escape') { if (['PLAYING', 'GAME', 'RESULT', 'INTRO', 'LOADING'].includes(gameState)) { console.log("Escape 按下，準備返回選單..."); handleBackToSelectClick(); return; } }

    const keyIndex = KEY_MAPPINGS.indexOf(keyCode);
    if (keyIndex !== -1) {
        if (!keyStates[keyCode]) {
            keyStates[keyCode] = true;
             if (isPlaying && gameLoopRunning) {
                 activeLaneFlashes.push({ laneIndex: keyIndex, startTime: currentSongTime, duration: LANE_FLASH_DURATION });
             }
             if (isPlaying && gameLoopRunning && currentSongTime > 0 && baseScorePerPerfect > 0) { // Check baseScore > 0
                const pressTime = currentSongTime;
                let bestNote = null;
                let minTimeDiff = Infinity;
                loadedNotes.forEach(note => { if (note.column === keyIndex && !note.judged && note.isActive) { const timeDiff = pressTime - note.targetTime; if (Math.abs(timeDiff) < JUDGE_WINDOW_MISS + 0.1) { if (Math.abs(timeDiff) < Math.abs(minTimeDiff)) { minTimeDiff = timeDiff; bestNote = note; } } } });

                if (bestNote) {
                    const absTimeDiff = Math.abs(minTimeDiff);
                    let judgmentText = '';
                    let scoreToAdd = 0; // Use float for intermediate calculation
                    let particleCount = 0;
                    let particleColor = '';

                    if (absTimeDiff <= JUDGE_WINDOW_PERFECT) {
                        judgmentText = 'Perfect'; scoreToAdd = baseScorePerPerfect; // 100%
                        combo++; judgmentCounts.perfect++; particleCount = PARTICLE_COUNT_PERFECT; particleColor = COLOR_PERFECT_PARTICLE;
                    } else if (absTimeDiff <= JUDGE_WINDOW_GREAT) {
                        judgmentText = 'Great'; scoreToAdd = baseScorePerPerfect * 0.5; // 50%
                        combo++; judgmentCounts.great++; particleCount = PARTICLE_COUNT_GREAT; particleColor = COLOR_GREAT_PARTICLE;
                    } else if (absTimeDiff <= JUDGE_WINDOW_GOOD) {
                        judgmentText = 'Good'; scoreToAdd = baseScorePerPerfect * 0.3; // 30%
                        combo++; judgmentCounts.good++; particleCount = PARTICLE_COUNT_GOOD; particleColor = COLOR_GOOD_PARTICLE;
                    }

                    if (judgmentText) {
                         console.log(`判定: ${judgmentText}(+${scoreToAdd.toFixed(2)}) C:${combo} (T:${minTimeDiff.toFixed(3)}s) ID:${bestNote.id}`);
                         bestNote.judged = true; bestNote.isActive = false;
                         lastJudgment = { text: judgmentText, time: currentSongTime, column: keyIndex };
                         score += scoreToAdd; // Add potentially fractional score
                         maxCombo = Math.max(maxCombo, combo);
                         playKeysound();

                         // Trigger particle effects
                         const particleOriginX = getInterpolatedX(keyIndex + 0.5, JUDGMENT_LINE_Y); const particleOriginY = JUDGMENT_LINE_Y;
                         const newParticleEffect = { type: judgmentText, particles: [] };
                         for (let i = 0; i < particleCount; i++) { const angle = Math.random() * Math.PI * 2; const speed = PARTICLE_BASE_SPEED + Math.random() * PARTICLE_RANDOM_SPEED; const lifetime = PARTICLE_MIN_LIFETIME + Math.random() * (PARTICLE_MAX_LIFETIME - PARTICLE_MIN_LIFETIME); const size = PARTICLE_BASE_SIZE + Math.random() * PARTICLE_RANDOM_SIZE; const angularVelocity = (Math.random() - 0.5) * 2 * PARTICLE_ANGULAR_VELOCITY_RANGE; newParticleEffect.particles.push({ x: particleOriginX, y: particleOriginY, vx: Math.cos(angle) * speed, vy: Math.sin(angle) * speed, rotation: Math.random() * Math.PI * 2, angularVelocity: angularVelocity, size: size, color: particleColor, alpha: 1.0, startTime: currentSongTime, lifetime: lifetime }); }
                         activeHitEffects.push(newParticleEffect);

                         // Trigger ring effect
                         const ringCenterX = particleOriginX; const ringCenterY = particleOriginY;
                         const ringStartWidth = getInterpolatedX(keyIndex + 1, JUDGMENT_LINE_Y) - getInterpolatedX(keyIndex, JUDGMENT_LINE_Y);
                         activeRingEffects.push({ centerX: ringCenterX, centerY: ringCenterY, startWidth: ringStartWidth, startTime: currentSongTime, duration: RING_EFFECT_DURATION });

                    } else { console.log(`空敲或時機過差 (T:${minTimeDiff.toFixed(3)}s) ID:${bestNote.id}`); }
                } else { console.log(`空敲 Lane ${keyIndex + 1}`); }
            }
        }
    }
});
window.addEventListener('keyup', function(event) { const keyCode = event.code; if (KEY_MAPPINGS.includes(keyCode)) { if (keyStates[keyCode]) { keyStates[keyCode] = false; } } });
function handleSongSelect(event) { if (gameState !== 'SELECTING') { console.warn("Attempted song selection while not in SELECTING state."); return; } const songItem = event.currentTarget; const songData = availableSongs.find(song => song.id === songItem.dataset.songId); if (songData) { startGame(songData); } else { console.error("選中的歌曲數據無效！", songItem.dataset); alert("選擇的歌曲資料似乎有問題，請稍後再試。"); } }
let resizeTimeout; window.addEventListener('resize', () => { clearTimeout(resizeTimeout); resizeTimeout = setTimeout(() => { resizeCanvas(); drawGameBackground(); }, 100); });
function handleBackToSelectClick() { /* ... (no change) ... */ console.log(`返回按鈕/Escape 觸發... 當前狀態: ${gameState}`); const currentState = gameState; const cleanupAndGoToSelect = () => { console.log("執行清理並返回選單...")
if (isPlaying) { if (audioSource) { try { audioSource.stop(); } catch(e) {console.warn("停止音源時出錯(可能已停止):", e);} audioSource.disconnect(); audioSource = null; } isPlaying = false; } gameLoopRunning = false; isAudioLoading = false; isAudioReady = false; isChartLoading = false; isChartReady = false; audioBuffer = null; chartData = null; loadedNotes = []; selectedSongData = null; activeHitEffects = []; activeLaneFlashes = []; activeRingEffects = []; songBgImage = null; isSongBgLoading = false; isSongBgReady = false; gameInfoIllustration = null; gameInfoIllustrationSrc = ''; showScreen('SELECTING'); }; switch (currentState) { case 'RESULT': console.log("從結算畫面返回，開始淡出..."); resultScreen.classList.remove('visible'); setTimeout(cleanupAndGoToSelect, 500); break; case 'INTRO': console.log("從 Intro 畫面返回，開始淡出..."); introScreen.classList.remove('visible'); setTimeout(cleanupAndGoToSelect, 500); break; case 'LOADING': console.log("從載入畫面返回..."); cleanupAndGoToSelect(); break; case 'PLAYING': case 'GAME': console.log("從遊戲中返回..."); cleanupAndGoToSelect(); break; case 'SELECTING': console.log("已經在選單畫面，無需操作。"); break; default: console.log(`在 ${currentState} 狀態下觸發返回，未定義明確操作，執行預設清理。`); cleanupAndGoToSelect(); break; } }

// =============================================================================
// 速度控制函數
// =============================================================================
function updateSpeedDisplay() { /* ... (no change) ... */ if (speedDisplay) { speedDisplay.textContent = `x${speedMultiplier.toFixed(2)}`; } }
function increaseSpeed() { /* ... (no change) ... */ if (speedMultiplier < MAX_SPEED_MULTIPLIER) { speedMultiplier = parseFloat((speedMultiplier + SPEED_ADJUST_STEP).toFixed(2)); noteAppearTimeOffset = BASE_NOTE_APPEAR_TIME_OFFSET / speedMultiplier; updateSpeedDisplay(); console.log(`速度增加到: x${speedMultiplier}, Offset: ${noteAppearTimeOffset.toFixed(3)}s`); } else { console.log("已達到最大速度"); } }
function decreaseSpeed() { /* ... (no change) ... */ if (speedMultiplier > MIN_SPEED_MULTIPLIER) { speedMultiplier = parseFloat((speedMultiplier - SPEED_ADJUST_STEP).toFixed(2)); speedMultiplier = Math.max(MIN_SPEED_MULTIPLIER, speedMultiplier); noteAppearTimeOffset = BASE_NOTE_APPEAR_TIME_OFFSET / speedMultiplier; updateSpeedDisplay(); console.log(`速度減少到: x${speedMultiplier}, Offset: ${noteAppearTimeOffset.toFixed(3)}s`); } else { console.log("已達到最小速度"); } }

// =============================================================================
// 應用程式初始化與啟動
// =============================================================================
async function initializeApp() { /* ... (no change) ... */ console.log("應用程式初始化..."); resizeCanvas(); updateSpeedDisplay(); increaseSpeedButton.addEventListener('click', increaseSpeed); decreaseSpeedButton.addEventListener('click', decreaseSpeed); songListContainer.innerHTML = '<p>正在載入歌曲列表...</p>'; try { const response = await fetch('songlist.json'); if (!response.ok) throw new Error(`無法載入 songlist.json: ${response.statusText}`); availableSongs = await response.json(); console.log(`歌曲列表載入完成，共 ${availableSongs.length} 首歌。`); populateSongList(); showScreen('SELECTING'); } catch (error) { console.error("初始化失敗 (載入歌曲列表時):", error); if (songListContainer) songListContainer.innerHTML = `<p style="color: red;">錯誤：無法載入歌曲列表。<br>${error.message}</p>`; alert(`初始化失敗:\n${error.message}`); showScreen('SELECTING'); } }

window.addEventListener('DOMContentLoaded', initializeApp);
import utime
import _thread
import osTimer
import gc
from misc import Power
from queue import Queue
from machine import RTC, UART, Pin
import ujson
import modem
import sim

try:
    from settings import Settings
    from settings_user import UserConfig
    from battery import Battery
    from history import History
    from logging import getLogger
    from net_manage import NetManager
    from thingsboard import TBDeviceMQTTClient
    from power_manage import PowerManage, PMLock
    from location import GNSS, GNSSBase, CellLocator, WiFiLocator, CoordinateSystemConvert
    from lcd_control import LCD_CONTROL
    from modbus import Modbus
    from packet_constructor import CANPacket
    from sms_config import SMSConfigHandler
except ImportError:
    from usr.settings import Settings
    from usr.settings_user import UserConfig
    from usr.battery import Battery
    from usr.history import History
    from usr.logging import getLogger
    from usr.net_manage import NetManager
    from usr.thingsboard import TBDeviceMQTTClient
    from usr.power_manage import PowerManage, PMLock
    from usr.location import GNSS, GNSSBase, CellLocator, WiFiLocator, CoordinateSystemConvert
    from usr.lcd_control import LCD_CONTROL
    from usr.modbus import Modbus
    from usr.packet_constructor import CANPacket
    from usr.sms_config import SMSConfigHandler

log = getLogger(__name__)

# Firmware release version: increment this on every release.
FIRMWARE_VERSION = "1.1.0"

# How long after load_min_max() runs at boot to ignore MSPM0's own boot-time BB01/BB02 reports.
BOOT_SETTLE_SEC = 10

# UART silence after which MSPM0 is reported Not Connected.
MSPM0_OFFLINE_SEC = 30

# Persisted board/MSPM0 connection, uptime/downtime, reboot count. Survives power cuts.
BOARD_HEALTH_PATH = "/usr/board_health.json"
BOARD_HEALTH_TMP_PATH = "/usr/board_health.tmp"

# Server 2 (optional second MQTT link) - min free heap required to enable it.
SERVER2_MIN_FREE_MEM = 60000

# Global variables for sensor data
FLOW_METER_VALUE = 0
PRESSURE_VALUE = 0
PH_SENSOR_VALUE = 0
TDS_VALUE = 0
DO_VALUE = 0
VALVE_STATUS = 0
BATTERY_LEVEL = 0
POWER_OUTPUT = 0
RSSI_SIM1 = 0
RSSI_SIM2 = 0
LOCATION_VALUE = "12.925880, 77.518082"
PH_UPDATE_VALUE = 0
NITRATE_VAL = 0
ANALOG_VAL = 0
CHLORINE_VAL = 0
BATT_CAP = 0
BATT_VOLT = 0
BATT_CURR = 0
BATTERY_LEVEL = 0
POWER_OUTPUT = 0

# Sensor error state tracking
ANALOG_ERR = False
PH_ERR = False
TDS_ERR = False
CHLORINE_ERR = False
NITRATE_ERR = False
BATT_CAP_ERR = False
BATT_VOLT_ERR = False
BATT_CURR_ERR = False
SERVER_STATUS = "Disconnected"
LEARN_MODE = 0
ANALOG_CHANNELS = [0, 0, 0, 0, 0, 0, 0, 0]
IMEI = ""
IMSI = ""

# SERVER CONFIG — edit these directly.

class Tracker:

    def __init__(self):
        self.__server = None
        self.__server2 = None                    # optional second MQTT link
        self.__server2_cfg = None                # dict from SMSConfigHandler.load_server2_status()
        self.__server2_reconn_timer = osTimer()
        self.__server2_reconn_count = 0
        self.__server2_conn_tag = 0
        self.__server2_state = "DISABLED"        # DISABLED | CONNECTING | CONNECTED | DISCONNECTED | REFUSED LOW MEMORY
        self.__server_ota = None
        self.__battery = None
        self.__history = None
        self.__gnss = None
        self.__cell = None
        self.__wifi = None
        self.__csc = None
        self.__net_manager = None
        self.__settings = None
        self.__lcd = None
        self.__modbus = None
        self.__serial = None
        self.__serial_tid = None
        self.__serial_buffer = bytearray()
        self.__sms_config = None

        self.__business_lock = PMLock("block")
        self.__business_tid = None
        self.__business_rtc = RTC()
        self.__business_queue = Queue()
        self.__business_tag = 0
        self.__server_ota_flag = 0
        self.__server_reconn_timer = osTimer()
        self.__modbus_timer = osTimer()
        # Placeholders until SMSConfigHandler.load_timer_config() overwrites these at boot.
        self.__cloud_time_sec = 10
        self.__modbus_interval_ms = 240000
        self.__display_timer = osTimer()
        self.__display_resume_timer = osTimer()
        self.__gpio_timer = osTimer()
        self.__server_conn_tag = 0
        self.__server_reconn_count = 0
        self.__reset_tag = 0
        self.page = 1

        # Business-thread watchdog: restarts/recovers if MQTT I/O ever hangs the single business thread.
        self.__business_tag_time = 0
        self.__business_watchdog_timer = osTimer()
        self.__business_recovery_stage = 0

        # Min/Max/Current values for valve learning
        self.min_value = 25000
        self.max_value = 35000
        self.cur_value = 30000
        self.previous_valve_status = 0
        self.valve_changed_flag = False
        self.__last_save_time = 0
        # Set once, right after load_min_max() runs in running().
        self.__boot_settle_time = 0

        # Extra safety net alongside __boot_settle_time above.
        self.__boot_bb01_ignored = False
        self.__boot_bb02_ignored = False

        # Last valve % the immediate (serial-RX-thread) LCD path drew.
        self.__last_immediate_valve_pct = None

        # Valve control state
        self.__valve_control_in_progress = False
        self.__valve_control_target = 0
        self.__valve_control_start_time = 0

        # Locks for thread safety
        self.__serial_lock = _thread.allocate_lock()
        self.__serial_tx_lock = _thread.allocate_lock()
        self.__valve_lock = _thread.allocate_lock()
        self.__display_lock = _thread.allocate_lock()
        self.__file_lock = _thread.allocate_lock()

        # Pre-built flow-ack (BBFF) sent to MSPM0 the instant an AA10 packet arrives.
        self.__flow_ack_bytes = CANPacket(
            interface_type=0x01, can_cmd=0xBBFF,
            data=list((20).to_bytes(8, 'little')), seq_id=1234, crc_16=1234).to_bytes()

        # Serial watchdog
        self.__serial_last_rx_time = 0
        self.__serial_watchdog_timer = osTimer()
        self.__serial_recovery_in_progress = False
        self.__serial_consecutive_errors = 0

        # Learn mode tracking
        self.__previous_learn_mode = 0
        # Running min/max sensed continuously while LEARN_MODE==1.
        self.__learn_session_min = None
        self.__learn_session_max = None
        self.__learn_session_samples = 0
        # Snapshot taken at the moment learning is switched off, for the exit page.
        self.__learn_last_min = None
        self.__learn_last_max = None
        self.__learn_last_samples = 0
        self.__learn_last_ok = False

        # Display timer suspension
        self.__display_suspended = False

        # Memory monitoring
        self.__mem_check_timer = osTimer()
        self.__last_free_mem = 0

        # Flow meter base offset.
        self.__flow_base = 0
        self.__flow_base_loaded = False
        self.__flow_lock = _thread.allocate_lock()
        # Most recent raw AA10 reading seen, for FLOW,<value> SMS calibration.
        self.__last_raw_flow_value = 0

        # Flow-meter update throttling: only while valve is open, at most once a minute.
        self.__last_flow_update_time = 0
        self.__flow_meter_valve_was_open = False

        # Water-leakage detection: valve closed but raw flow rising.
        self.__leak_samples = []
        self.__leak_sample_count = 10
        self.__leak_min_delta = 5   # min net rise across window to count as a leak, not noise
        self.__leak_alert_active = False

        # Generic failure-alert framework (SIM/network/MQTT/etc share this dict).
        self.__active_alerts = {}

        # SIM/network health check debounce state.
        self.__sim_fail_count = 0
        self.__net_reg_fail_count = 0
        self.__data_call_fail_count = 0
        self.__weak_signal_fail_count = 0
        self.__net_health_check_timer = osTimer()
        self.__net_health_debounce_threshold = 3    # consecutive failed checks before raising
        self.__net_health_check_interval_ms = 60000       # slow poll while healthy
        self.__net_health_check_fast_interval_ms = 5000   # fast poll while any issue active

        # Some modems don't auto re-scan the SIM on a hot swap - forces a reconnect periodically.
        self.__sim_recovery_next_attempt_at = self.__net_health_debounce_threshold * 2
        self.__sim_recovery_retry_step = 6

        # MQTT reconnect-count alert thresholds (earlier warnings than the 20/40 recovery actions).
        self.__mqtt_warning_reconn_count = 5
        self.__mqtt_critical_reconn_count = 15

        # Don't alert on MQTT connectivity until we've connected at least once.
        self.__server_ever_connected = False

        # Board/MSPM0 health for telemetry - reuses the 15s serial watchdog + loc_report cycle, no extra timers.
        self.__boot_ticks_ms = utime.ticks_ms()
        self.__mspm0_last_packet_time = 0
        self.__mspm0_connected = False
        # Board uptime/downtime tracking, persisted across reboots.
        self.__board_last_downtime_sec = 0
        self.__board_total_uptime_sec = 0
        self.__board_total_downtime_sec = 0
        self.__board_last_seen_epoch = 0
        self.__last_health_save_time = 0
        self.__last_persisted_board_connection = ""
        self.__last_persisted_mspm0_connection = ""
        self.__board_reboot_count = 0

    def __business_start(self):
        if not self.__business_tid or (self.__business_tid and not _thread.threadIsRunning(self.__business_tid)):
            _thread.stack_size(0x7000)
            self.__business_tid = _thread.start_new_thread(self.__business_running, ())

    def __business_stop(self):
        self.__business_tid = None
        self.__serial_stop()
        self.__modbus_timer.stop()
        self.__gpio_timer.stop()
        self.__display_timer.stop()
        self.__serial_watchdog_timer.stop()
        self.__mem_check_timer.stop()
        self.__business_watchdog_timer.stop()
        log.debug("Business thread and all timers stopped")

    def __business_running(self):
        while self.__business_tid is not None or self.__business_queue.size() > 0:
            data = self.__business_queue.get()
            with self.__business_lock:
                self.__business_tag = 1
                self.__business_tag_time = utime.time()
                try:
                    self.__business_dispatch(data)
                except Exception as e:
                    # Never let a bad task kill the business thread.
                    log.error("Business task %s failed: %s" % (str(data[:2]), str(e)))
                    import sys
                    sys.print_exception(e)
                finally:
                    self.__business_tag = 0

    def __business_dispatch(self, data):
        if data[0] == 0:
            if data[1] == "loc_report":
                self.__loc_report()
                if self.valve_changed_flag:
                    self.valve_changed_flag = False
                    log.debug("Valve changed flag cleared after telemetry sent")
            elif data[1] == "server_connect":
                self.__server_connect()
            elif data[1] == "server2_connect":
                self.__server2_connect()
            elif data[1] == "server2_apply":
                self.__server2_apply()
            elif data[1] == "modbus_read":
                self.__read_modbus_data()
            elif data[1] == "serial_data":
                self.__process_serial_data(data[2])
            elif data[1] == "serial_send":
                self.__send_serial_data(data[2])
            elif data[1] == "net_health_check":
                # Routed through the queue - must not run on the osTimer thread that schedules it.
                self.__net_health_check(None)
            elif data[1] == "display_valve_page":
                if self.__lcd:
                    with self.__display_lock:
                        self.__display_page_4()
                    log.debug("Valve page displayed immediately on status change")
                    self.__suspend_display_timer()
            elif data[1] == "display_learn_exit":
                if self.__lcd:
                    with self.__display_lock:
                        self.__display_learn_exit_message()
                    log.debug("Learn mode exit message displayed")
                    self.__suspend_display_timer()
        if data[0] == 1:
            self.__server_option(data[1])
        if data[0] == 2:
            # RPC from server 2: reply goes back on server 2.
            if self.__server2 is not None:
                self.__server_option(data[1], self.__server2)
            else:
                log.warning("RPC from server 2 dropped: link no longer exists")

    def __business_watchdog_check(self, args):
        try:
            # Dead thread: restart in place. Stuck thread: escalate below.
            if self.__business_tid is not None and not _thread.threadIsRunning(self.__business_tid):
                log.error("Business thread died; restarting it")
                self.__business_tag = 0
                self.__business_recovery_stage = 0
                self.__business_start()
                return
            if self.__business_tag != 1:
                self.__business_recovery_stage = 0
                return
            stuck = utime.time() - self.__business_tag_time
            if stuck > 90 and self.__business_recovery_stage == 0:
                self.__business_recovery_stage = 1
                log.error("Business thread stuck %ds; attempting modem recovery" % int(stuck))
                _thread.stack_size(0x1000)
                _thread.start_new_thread(self.__modem_recover, ())
            elif stuck > 180 and self.__business_recovery_stage == 1:
                self.__business_recovery_stage = 2
                log.error("Business thread still stuck %ds; forcing power restart" % int(stuck))
                _thread.stack_size(0x1000)
                _thread.start_new_thread(self.__power_restart, ())
        except Exception as e:
            log.error("Business watchdog error: %s" % str(e))

    def __generate_timestamp(self):
        try:
            t = utime.localtime()
            return "{:02d}/{:02d}/{:02d},{:02d}:{:02d}:{:02d}+05:30".format(
                t[2], t[1], t[0] % 100, t[3], t[4], t[5]
            )
        except Exception:
            return "15/05/25,16:13:00+05:30"

    def __loc_report(self):
        if self.__server is None:
            # Can be queued before self.__server exists (early boot race).
            log.debug("loc_report skipped - server not yet initialized (early boot)")
            return
        loc_state, properties = self.__get_loc_data()
        global VALVE_STATUS, FLOW_METER_VALUE, ANALOG_VAL, PH_SENSOR_VALUE
        global TDS_VALUE, CHLORINE_VAL, NITRATE_VAL, DO_VALUE
        global VALVE_STATUS, BATTERY_LEVEL, POWER_OUTPUT
        global RSSI_SIM1, RSSI_SIM2, LOCATION_VALUE
        global ANALOG_CHANNELS
        global IMEI, IMSI, BATT_CURR
        loc_state = 1
        if loc_state == 1:
            res = False
            s1_up = self.__server.status
            s2_up = self.__server2 is not None and self.__server2.status
            if s1_up or s2_up:
                data = {
                    "timestamp":    self.__generate_timestamp(),
                    "FlowMeter":    FLOW_METER_VALUE,
                    "Pressure":     ANALOG_VAL,
                    "PH Sensor":    PH_SENSOR_VALUE,
                    "TDS":          TDS_VALUE,
                    "Chlorine":     CHLORINE_VAL,
                    "Nitrate":      NITRATE_VAL,
                    "BATT_VOLT":    BATT_VOLT,
                    "Load Current": BATT_CURR,
                    "BATT_CAP":     BATT_CAP,
                    "DO":           DO_VALUE,
                    "ch0": ANALOG_CHANNELS[0],
                    "ch1": ANALOG_CHANNELS[1],
                    "ch2": ANALOG_CHANNELS[2],
                    "ch3": ANALOG_CHANNELS[3],
                    "ch4": ANALOG_CHANNELS[4],
                    "ch5": ANALOG_CHANNELS[5],
                    "ch6": ANALOG_CHANNELS[6],
                    "ch7": ANALOG_CHANNELS[7],
                    "Valve Status":  VALVE_STATUS,
                    "Battery Level": BATTERY_LEVEL,
                    "Power Output":  POWER_OUTPUT,
                    "RSSI SIM1":     RSSI_SIM1,
                    "RSSI SIM2":     RSSI_SIM2,
                    "location":      LOCATION_VALUE,
                    "IMEI":          IMEI,
                    "IMSI":          IMSI,
                    "Leak Alert":    self.__leak_alert_active,
                    "Leak Message":  "Water leakage detected - valve closed but flow rising" if self.__leak_alert_active else "",
                    "Failure Alerts": self.__get_active_generic_alerts()
                }
                # Board/MSPM0 status + uptime/downtime + reboot count, folded into telemetry.
                data.update(self.__board_health_telemetry(s1_up or s2_up))
                if s1_up:
                    res = self.__server.send_telemetry(data)
                if s2_up:
                    # Server 2 is telemetry-only and best-effort.
                    if not self.__server2.send_telemetry(data):
                        log.warning("Server 2 telemetry publish failed")
            if not res:
                self.__history.write([properties])

        if self.__server.status:
            self.__history_report()
        else:
            log.warning("Server not connected during report; triggering reconnect")
            self.server_connect(None)

        if self.__server2 is not None and not self.__server2.status:
            self.server2_connect(None)

        self.__touch_board_heartbeat()
        self.__set_rtc(self.__cloud_time_sec, self.loc_report)

    def __history_report(self):
        failed_datas = []
        his_datas = self.__history.read()
        if his_datas["data"]:
            for item in his_datas["data"]:
                res = self.__server.send_telemetry(item)
                if not res:
                    failed_datas.append(item)
        if failed_datas:
            self.__history.write(failed_datas)

    def __get_loc_data(self):
        loc_state = 0
        loc_data = {"Longitude": 0.0, "Latitude": 0.0, "Altitude": 0.0, "Speed": 0.0}
        try:
            if self.__valve_control_in_progress:
                log.debug("GPS read skipped - valve control in progress")
                return (loc_state, loc_data)

            loc_cfg  = self.__settings.read("loc")
            user_cfg = self.__settings.read("user")
            if user_cfg["loc_method"] & UserConfig._loc_method.gps:
                if self.__gnss is None:
                    log.error("GNSS module not initialized")
                else:
                    res = self.__gnss.read()
                    log.debug("gnss read %s" % str(res))
                    if res and res.get("state") == "A":
                        loc_data["Latitude"]  = float(res["lat"]) * (1 if res["lat_dir"] == "N" else -1)
                        loc_data["Longitude"] = float(res["lng"]) * (1 if res["lng_dir"] == "E" else -1)
                        loc_data["Altitude"]  = res.get("altitude", 0.0)
                        loc_data["Speed"]     = res.get("speed", 0.0)
                        loc_state = 1
                    elif res and res.get("state") == "V":
                        log.debug("GPS no fix yet (satellites: %s)" % res.get("satellites", "0"))
                    else:
                        log.debug("GPS data invalid or empty")
            if loc_state == 0 and user_cfg["loc_method"] & UserConfig._loc_method.cell:
                res = self.__cell.read()
                if isinstance(res, tuple):
                    loc_data["Longitude"] = res[0]
                    loc_data["Latitude"]  = res[1]
                    loc_state = 1
            if loc_state == 0 and user_cfg["loc_method"] & UserConfig._loc_method.wifi:
                res = self.__wifi.read()
                if isinstance(res, tuple):
                    loc_data["Longitude"] = res[0]
                    loc_data["Latitude"]  = res[1]
                    loc_state = 1
            if loc_state == 1 and loc_cfg["map_coordinate_system"] == "GCJ02":
                lng, lat = self.__csc.wgs84_to_gcj02(loc_data["Longitude"], loc_data["Latitude"])
                loc_data["Longitude"] = lng
                loc_data["Latitude"]  = lat
        except Exception as e:
            log.error("Error in __get_loc_data: %s" % str(e))
        return (loc_state, loc_data)

    def __set_rtc(self, period, callback):
        self.__business_rtc.enable_alarm(0)
        if callback and callable(callback):
            self.__business_rtc.register_callback(callback)
        atime = utime.localtime(utime.mktime(utime.localtime()) + period)
        alarm_time = (atime[0], atime[1], atime[2], atime[6], atime[3], atime[4], atime[5], 0)
        _res = self.__business_rtc.set_alarm(alarm_time)
        log.debug("alarm_time: %s, set_alarm res %s." % (str(alarm_time), _res))
        return self.__business_rtc.enable_alarm(1) if _res == 0 else -1

    # Load broker credentials from file, then fall back to settings.
    def __read_server_status_json(self):
        try:
            with open("/usr/server_status.json", "r") as f:
                data = ujson.load(f)
            host = data.get("host")
            port = data.get("port")
            username = data.get("username")
            if host and port and username:
                return host, port, username
        except Exception as e:
            log.warning("Cannot read server_status.json: %s" % str(e))
        cfg = self.__settings.read("server")
        return cfg.get("host"), cfg.get("port"), cfg.get("username")

    def __server_connect(self):
        global SERVER_STATUS
        try:
            if self.__net_manager.net_status():
                host, port, username = self.__read_server_status_json()

                log.info("Connecting to server: host=%s port=%s username=%s" % (
                    host, port, username))

                try:
                    self.__server.disconnect()
                except Exception as e:
                    log.warning("Disconnect error (ignored): %s" % str(e))

                try:
                    server_cfg = self.__settings.read("server")
                    server_cfg["host"]     = host
                    server_cfg["port"]     = port
                    server_cfg["username"] = username
                    self.__server = TBDeviceMQTTClient(**server_cfg)
                    self.__server.set_callback(self.server_callback)
                    log.info("Server object reinitialized with new credentials")
                except Exception as e:
                    log.error("Failed to reinitialize server object: %s" % str(e))

                try:
                    self.__server.connect()
                except Exception as e:
                    log.error("server.connect() raised: %s" % str(e))

            # Live SIM/network check, reused for alerting and retry pacing.
            _sim_ok_now = False
            _net_ok_now = False
            try:
                _sim_ok_now = (self.__net_manager.sim_status() == 1)
                if _sim_ok_now:
                    _net_ok_now = self.__net_manager.net_state()
            except Exception as e:
                log.error("Live SIM/network check during server_connect failed: %s" % str(e))
            _net_layer_problem_now = (not _sim_ok_now) or (not _net_ok_now)

            if not self.__server.status:
                log.debug("Server not connected")
                SERVER_STATUS = "Disconnected"

                if _net_layer_problem_now:
                    # Root cause is SIM/network, not the broker.
                    self.__server_reconn_timer.stop()
                    self.__server_reconn_timer.start(10 * 1000, 0, self.server_connect)
                    self.__server_reconn_count = 0
                    self.__clear_generic_alert(
                        "mqtt_broker_unreachable",
                        "suppressed - underlying SIM/network issue is root cause")
                else:
                    self.__server_reconn_timer.stop()
                    self.__server_reconn_timer.start(60 * 1000, 0, self.server_connect)
                    self.__server_reconn_count += 1

                    # Earlier warning levels than the 20/40 recovery-action thresholds below.
                    if self.__server_ever_connected:
                        # Only alert once we've connected before - boot attach window is expected to fail.
                        if self.__server_reconn_count >= self.__mqtt_critical_reconn_count:
                            self.__raise_generic_alert(
                                "mqtt_broker_unreachable",
                                "Connection failed",
                                "CRITICAL")
                        elif self.__server_reconn_count >= self.__mqtt_warning_reconn_count:
                            self.__raise_generic_alert(
                                "mqtt_broker_unreachable",
                                "Connection failed",
                                "WARNING")

                    # Modem-only recovery first; power restart is last resort.
                    if self.__server_reconn_count == 20:
                        log.warning("20 reconnect failures: attempting modem-only recovery")
                        _thread.stack_size(0x1000)
                        _thread.start_new_thread(self.__modem_recover, ())
                    elif self.__server_reconn_count >= 40:
                        log.error("40 reconnect failures: last-resort power restart")
                        _thread.stack_size(0x1000)
                        _thread.start_new_thread(self.__power_restart, ())
            else:
                self.__server_reconn_count = 0
                SERVER_STATUS = "Connected"
                self.__server_ever_connected = True
                log.info("Server connected successfully")
                self.__clear_generic_alert("mqtt_broker_unreachable", "MQTT reconnected successfully")
                self.__touch_board_heartbeat()
                self.__business_queue.put((0, "loc_report"))

        except Exception as e:
            log.error("__server_connect failed unexpectedly: %s" % str(e))
            SERVER_STATUS = "Disconnected"
            try:
                self.__server_reconn_timer.stop()
                self.__server_reconn_timer.start(60 * 1000, 0, self.server_connect)
            except Exception as e2:
                log.error("Failed to re-arm reconnect timer: %s" % str(e2))
        finally:
            # Guarantees __server_conn_tag never gets permanently stuck.
            self.__server_conn_tag = 0

    def __server2_apply(self):
        # Runs after an SMS changes server2_status.json, and once at boot. Never raises.
        try:
            self.__server2_teardown()
            cfg = self.__sms_config.load_server2_status() if self.__sms_config else None
            self.__server2_cfg = cfg
            if not cfg or not cfg.get("enabled"):
                self.__server2_state = "DISABLED"
                log.info("Server 2 disabled")
                return
            if not (cfg.get("host") and cfg.get("port") and cfg.get("username")):
                self.__server2_state = "DISABLED"
                log.warning("Server 2 enabled but not configured")
                return
            gc.collect()
            free = gc.mem_free()
            if free < SERVER2_MIN_FREE_MEM:
                self.__server2_state = "REFUSED LOW MEMORY"
                log.error("Server 2 not enabled: free memory %d < %d" % (free, SERVER2_MIN_FREE_MEM))
                return
            server_cfg = dict(self.__settings.read("server"))   # copy - Settings.read() returns internal dict by reference
            server_cfg["host"]      = cfg["host"]
            server_cfg["port"]      = cfg["port"]
            server_cfg["username"]  = cfg["username"]
            # Distinct client id - same id would kick the server-1 session.
            server_cfg["client_id"] = "%s_2" % str(server_cfg.get("client_id", "1234"))
            self.__server2 = TBDeviceMQTTClient(**server_cfg)
            self.__server2.set_callback(self.server2_callback)
            self.__server2_reconn_count = 0
            self.__server2_state = "CONNECTING"
            log.info("Server 2 configured: host=%s port=%s (free mem %d)" % (cfg["host"], cfg["port"], free))
            self.server2_connect(None)
        except Exception as e:
            log.error("Server 2 apply failed: %s" % str(e))
            self.__server2_state = "DISCONNECTED"

    def __server2_teardown(self):
        try:
            self.__server2_reconn_timer.stop()
        except Exception:
            pass
        if self.__server2 is not None:
            try:
                self.__server2.disconnect()
            except Exception as e:
                log.warning("Server 2 disconnect error (ignored): %s" % str(e))
            self.__server2 = None
            gc.collect()

    def __server2_connect(self):
        # Mirrors __server_connect's retry cadence but never escalates to modem/power recovery.
        try:
            if self.__server2 is None or not self.__server2_cfg or not self.__server2_cfg.get("enabled"):
                return
            if self.__net_manager.net_status():
                try:
                    self.__server2.disconnect()
                except Exception as e:
                    log.warning("Server 2 disconnect before reconnect (ignored): %s" % str(e))
                try:
                    self.__server2.connect()
                except Exception as e:
                    log.error("server2.connect() raised: %s" % str(e))

            _sim_ok_now = False
            _net_ok_now = False
            try:
                _sim_ok_now = (self.__net_manager.sim_status() == 1)
                if _sim_ok_now:
                    _net_ok_now = self.__net_manager.net_state()
            except Exception as e:
                log.error("Live SIM/network check during server2_connect failed: %s" % str(e))
            _net_layer_problem_now = (not _sim_ok_now) or (not _net_ok_now)

            if not self.__server2.status:
                self.__server2_state = "DISCONNECTED"
                self.__server2_reconn_timer.stop()
                if _net_layer_problem_now:
                    self.__server2_reconn_count = 0
                    self.__server2_reconn_timer.start(10 * 1000, 0, self.server2_connect)
                else:
                    self.__server2_reconn_count += 1
                    self.__server2_reconn_timer.start(60 * 1000, 0, self.server2_connect)
                    log.warning("Server 2 not connected (attempt %d)" % self.__server2_reconn_count)
            else:
                self.__server2_reconn_count = 0
                self.__server2_state = "CONNECTED"
                log.info("Server 2 connected successfully")
        except Exception as e:
            log.error("__server2_connect failed unexpectedly: %s" % str(e))
            self.__server2_state = "DISCONNECTED"
            try:
                self.__server2_reconn_timer.stop()
                self.__server2_reconn_timer.start(60 * 1000, 0, self.server2_connect)
            except Exception as e2:
                log.error("Failed to re-arm server 2 reconnect timer: %s" % str(e2))
        finally:
            self.__server2_conn_tag = 0

    def __server2_state_text(self):
        # Live state string for the PARAMS2# SMS reply.
        try:
            if self.__server2 is None:
                return self.__server2_state if self.__server2_state in ("DISABLED", "REFUSED LOW MEMORY") else "DISABLED"
            return "CONNECTED" if self.__server2.status else self.__server2_state
        except Exception:
            return "UNKNOWN"

    def __sms_server2_changed_callback(self):
        log.info("SMS: server 2 config changed, applying")
        self.__business_queue.put((0, "server2_apply"))

    def __modem_recover(self):
        try:
            log.info("Modem recovery: cycling modem function (no reboot)")
            if self.__net_manager:
                self.__net_manager.net_disconnect()
                utime.sleep(2)
                self.__net_manager.net_connect()
            self.server_connect(None)
        except Exception as e:
            log.error("Modem recovery failed: %s" % str(e))

    def __sim_recover(self):
        # Forces a modem reconnect to re-scan the SIM. Own thread - net_connect() can block up to 300s.
        try:
            log.info("SIM recovery: forcing modem reconnect to re-detect SIM")
            if self.__net_manager:
                self.__net_manager.net_reconnect()
                self.server_connect(None)
        except Exception as e:
            log.error("SIM recovery cycle failed: %s" % str(e))

    def __sms_config_changed_callback(self):
        log.info("SMS config changed: queuing server reconnect")
        self.__business_queue.put((0, "server_connect"))

    def __refresh_valve_display(self):
        # Direct call, no queue hop - called from the business thread already, avoids LCD lag.
        if self.__lcd:
            with self.__display_lock:
                self.__display_page_4()
            self.__suspend_display_timer()

    def __refresh_learn_display(self):
        # Direct call, no queue hop, no waiting for the 5s display tick.
        if self.__lcd:
            with self.__display_lock:
                self.__display_page_learn()
            self.__suspend_display_timer()

    def __refresh_learn_exit_display(self):
        # Direct call, no queue hop, on learn-mode exit.
        if self.__lcd:
            with self.__display_lock:
                self.__display_learn_exit_message()
            self.__suspend_display_timer()

    def __update_valve_display_immediate(self, can_data):
        # Draws the LCD straight off the UART RX thread so a busy business thread can't lag it.
        global VALVE_STATUS, LEARN_MODE
        try:
            if LEARN_MODE == 1:
                # Business thread is already sensing this stream for the learn session.
                return

            data_bytes = bytes(can_data.data)
            raw_value  = int.from_bytes(data_bytes, 'little')

            with self.__valve_lock:
                if self.max_value > self.min_value and self.max_value > 0:
                    clamped    = max(self.min_value, min(raw_value, self.max_value))
                    percentage = (clamped - self.min_value) * 100.0 / (self.max_value - self.min_value)
                    percentage = max(0, min(100, percentage))
                else:
                    percentage = 0
                current_status = int(percentage)

            VALVE_STATUS = current_status

            if (self.__last_immediate_valve_pct is not None and
                    abs(current_status - self.__last_immediate_valve_pct) <= 1):
                # Not a meaningful change - keep the number accurate but don't jump the display.
                return

            self.__last_immediate_valve_pct = current_status
            self.__refresh_valve_display()
        except Exception as e:
            log.error("Immediate valve display update error: %s" % str(e))

    def __check_leak_detection(self, raw_flow_value):
        # Called per AA10 packet while VALVE_STATUS==0. Leak = whole window non-decreasing AND net rise > threshold.
        try:
            self.__leak_samples.append(raw_flow_value)
            if len(self.__leak_samples) > self.__leak_sample_count:
                self.__leak_samples = self.__leak_samples[-self.__leak_sample_count:]

            if len(self.__leak_samples) < self.__leak_sample_count:
                return

            non_decreasing = all(
                self.__leak_samples[i] <= self.__leak_samples[i + 1]
                for i in range(len(self.__leak_samples) - 1)
            )
            net_rise = self.__leak_samples[-1] - self.__leak_samples[0]

            if non_decreasing and net_rise > self.__leak_min_delta:
                if not self.__leak_alert_active:
                    self.__raise_leak_alert(self.__leak_samples[0], self.__leak_samples[-1])
            else:
                if self.__leak_alert_active:
                    self.__clear_leak_alert("trend broke - reading dropped or flattened out")
        except Exception as e:
            log.error("Leak detection error: %s" % str(e))

    def __raise_leak_alert(self, start_value, end_value):
        # Fires once on transition into alert. Forces LCD page + immediate telemetry push.
        self.__leak_alert_active = True
        log.error("WATER LEAKAGE DETECTED: valve closed but flow rose %d -> %d over %d samples" % (
            start_value, end_value, self.__leak_sample_count))
        if self.__lcd:
            with self.__display_lock:
                self.__display_leak_alert()
        self.__business_queue.put((0, "loc_report"))

    def __clear_leak_alert(self, reason):
        # Fires once on transition out of alert.
        self.__leak_alert_active = False
        log.info("Leak alert cleared: %s" % reason)
        self.__business_queue.put((0, "loc_report"))

    def __display_leak_alert(self):
        try:
            if self.__lcd:
                self.__lcd.display_string("!!  LEAK ALERT  !!", 1)
                self.__lcd.display_string("Valve CLOSED but", 2)
                self.__lcd.display_string("flow is rising", 3)
                self.__lcd.display_string("Check plumbing!", 4)
        except Exception as e:
            log.error("Leak alert page error: %s" % str(e))

    def __raise_generic_alert(self, code, message, severity="WARNING"):
        # Shared alert raise for SIM/network/MQTT/etc. Fires on transition-to-active or severity change only.
        try:
            existing = self.__active_alerts.get(code)
            if existing and existing.get("active") and existing.get("severity") == severity:
                return
            self.__active_alerts[code] = {
                "active": True,
                "severity": severity,
                "message": message,
                "raised_at": utime.time()
            }
            if severity == "CRITICAL":
                log.error("ALERT [%s] %s" % (code, message))
            else:
                log.warning("ALERT [%s] %s" % (code, message))
            if self.__server is not None:
                self.__business_queue.put((0, "loc_report"))
        except Exception as e:
            log.error("Error raising alert %s: %s" % (code, str(e)))

    def __clear_generic_alert(self, code, reason):
        # No-ops quietly if the alert was never active.
        try:
            existing = self.__active_alerts.get(code)
            if not existing or not existing.get("active"):
                return
            self.__active_alerts[code] = {
                "active": False,
                "severity": existing.get("severity", "WARNING"),
                "message": "",
                "raised_at": 0
            }
            log.info("ALERT CLEARED [%s]: %s" % (code, reason))
            if self.__server is not None:
                self.__business_queue.put((0, "loc_report"))
        except Exception as e:
            log.error("Error clearing alert %s: %s" % (code, str(e)))

    def __get_active_generic_alerts(self):
        # {code: message} for every currently active alert, for telemetry.
        try:
            return {k: v["message"] for k, v in self.__active_alerts.items() if v.get("active")}
        except Exception as e:
            log.error("Error collecting active alerts: %s" % str(e))
            return {}

    def __highest_severity_generic_alert(self):
        # Highest-severity active alert, ties broken by most recent. For the LCD.
        try:
            active = [(k, v) for k, v in self.__active_alerts.items() if v.get("active")]
            if not active:
                return None

            def _rank(item):
                _, v = item
                sev_rank = 1 if v.get("severity") == "CRITICAL" else 0
                return (sev_rank, v.get("raised_at", 0))

            active.sort(key=_rank, reverse=True)
            code, v = active[0]
            return (code, v.get("message", ""))
        except Exception as e:
            log.error("Error picking highest severity alert: %s" % str(e))
            return None

    def __display_generic_alert(self, code, message):
        # Generic 4-line alert page for anything in __active_alerts (leak alert has its own page).
        try:
            if self.__lcd:
                self.__lcd.display_string("!! ALERT: %s" % code[:9], 1)
                line2 = message[0:20]
                line3 = message[20:40]
                line4 = message[40:60]
                self.__lcd.display_string(line2, 2)
                self.__lcd.display_string(line3, 3)
                self.__lcd.display_string(line4, 4)
        except Exception as e:
            log.error("Generic alert page error: %s" % str(e))

    def __queue_net_health_check(self, args):
        # osTimer callback - only enqueues, must not touch the modem directly from this thread.
        self.__business_queue.put((0, "net_health_check"))

    def __net_health_check(self, args):
        # Layered SIM -> registration -> data-call check, each only evaluated if the layer above is healthy.
        try:
            if not self.__net_manager:
                return

            # Layer 1: SIM presence.
            sim_ok = False
            try:
                sim_ok = (self.__net_manager.sim_status() == 1)
            except Exception as e:
                log.error("SIM status check error: %s" % str(e))

            if sim_ok:
                _sim_was_failing = self.__sim_fail_count > 0
                self.__sim_fail_count = 0
                self.__sim_recovery_next_attempt_at = self.__net_health_debounce_threshold * 2
                self.__clear_generic_alert("sim_missing", "SIM detected OK")
                if _sim_was_failing:
                    log.info("SIM recovered - triggering immediate server reconnect")
                    self.server_connect(None)
            else:
                self.__sim_fail_count += 1
                if self.__sim_fail_count >= self.__net_health_debounce_threshold:
                    self.__raise_generic_alert(
                        "sim_missing",
                        "Network Issue! Check the SIM",
                        "CRITICAL")
                    # Force a modem reconnect if a hot-swapped SIM still isn't detected.
                    if self.__sim_fail_count >= self.__sim_recovery_next_attempt_at:
                        log.warning("SIM still not detected after %d checks - forcing modem reconnect to re-scan (retry #%d)" % (
                            self.__sim_fail_count,
                            (self.__sim_fail_count - (self.__net_health_debounce_threshold * 2)) // self.__sim_recovery_retry_step + 1))
                        self.__sim_recovery_next_attempt_at = self.__sim_fail_count + self.__sim_recovery_retry_step
                        _thread.stack_size(0x1000)
                        _thread.start_new_thread(self.__sim_recover, ())

            # Layer 2: network registration.
            if sim_ok:
                net_ok = False
                try:
                    net_ok = self.__net_manager.net_state()
                except Exception as e:
                    log.error("Network state check error: %s" % str(e))

                if net_ok:
                    _net_was_failing = self.__net_reg_fail_count > 0
                    self.__net_reg_fail_count = 0
                    self.__clear_generic_alert("net_unregistered", "Network registered OK")
                    if _net_was_failing:
                        log.info("Network registration recovered - triggering immediate server reconnect")
                        self.server_connect(None)
                else:
                    self.__net_reg_fail_count += 1
                    if self.__net_reg_fail_count >= self.__net_health_debounce_threshold:
                        self.__raise_generic_alert(
                            "net_unregistered",
                            "Network Issue! Check the SIM",
                            "CRITICAL")
            else:
                self.__net_reg_fail_count = 0
                self.__clear_generic_alert("net_unregistered", "suppressed - SIM issue is root cause")

            # Layer 3: data call.
            if sim_ok:
                try:
                    net_ok_for_call = self.__net_manager.net_state()
                except Exception:
                    net_ok_for_call = False
                if net_ok_for_call:
                    call_ok = False
                    try:
                        call_ok = self.__net_manager.call_state()
                    except Exception as e:
                        log.error("Data call state check error: %s" % str(e))

                    if call_ok:
                        self.__data_call_fail_count = 0
                        self.__clear_generic_alert("data_call_down", "Data call restored")
                    else:
                        self.__data_call_fail_count += 1
                        severity = "CRITICAL" if self.__data_call_fail_count >= (self.__net_health_debounce_threshold * 2) else "WARNING"
                        if self.__data_call_fail_count >= self.__net_health_debounce_threshold:
                            self.__raise_generic_alert(
                                "data_call_down",
                                "Network Issue! Check the SIM",
                                severity)
                else:
                    self.__data_call_fail_count = 0
                    self.__clear_generic_alert("data_call_down", "suppressed - registration issue is root cause")
            else:
                self.__data_call_fail_count = 0
                self.__clear_generic_alert("data_call_down", "suppressed - SIM issue is root cause")

            # Signal strength - independent early warning.
            try:
                csq = self.__net_manager.signal_csq()
                if csq == 99:
                    self.__weak_signal_fail_count += 1
                    if self.__weak_signal_fail_count >= self.__net_health_debounce_threshold:
                        self.__raise_generic_alert(
                            "weak_signal",
                            "Signal unknown/undetectable (CSQ=99)",
                            "WARNING")
                elif 0 <= csq <= 9:
                    self.__weak_signal_fail_count += 1
                    if self.__weak_signal_fail_count >= self.__net_health_debounce_threshold:
                        self.__raise_generic_alert(
                            "weak_signal",
                            "Weak signal (CSQ=%d)" % csq,
                            "WARNING")
                else:
                    self.__weak_signal_fail_count = 0
                    self.__clear_generic_alert("weak_signal", "Signal level OK")
            except Exception as e:
                log.error("Signal strength check error: %s" % str(e))

        except Exception as e:
            log.error("Net health check error: %s" % str(e))
        finally:
            # Poll fast while any issue is active/debouncing, slow otherwise.
            try:
                _any_alert_active = any(v.get("active") for v in self.__active_alerts.values())
                _any_fail_counters = (
                    self.__sim_fail_count > 0 or
                    self.__net_reg_fail_count > 0 or
                    self.__data_call_fail_count > 0 or
                    self.__weak_signal_fail_count > 0
                )
                _next_interval = (self.__net_health_check_fast_interval_ms
                                   if (_any_alert_active or _any_fail_counters)
                                   else self.__net_health_check_interval_ms)
                self.__net_health_check_timer.stop()
                self.__net_health_check_timer.start(_next_interval, 0, self.__queue_net_health_check)
            except Exception as e:
                log.error("Failed to reschedule net health check timer: %s" % str(e))

    def __server_option(self, args, server=None):
        link = server if server is not None else self.__server
        topic, data = args
        log.debug("topic[%s]data[%s]" % args)
        topic_str  = topic.decode()
        payload    = ujson.loads(data.decode())
        request_id = topic_str.split("/")[-1]
        method     = payload.get("method")
        params     = payload.get("params")

        if method == "setState":
            # Validate defensively - dashboard can send null/missing/non-numeric/out-of-range values.
            value = None
            try:
                value = int(params)
            except (TypeError, ValueError):
                log.error("setState rejected: invalid params %s" % repr(params))
            if value is not None and 0 <= value <= 100:
                log.debug("Setting state to: %d" % value)
                value_bytes = [value] + [0] * 7
                packet = CANPacket(interface_type=0x01, can_cmd=0xBB03, data=value_bytes, seq_id=1234, crc_16=1234)
                self.__business_queue.put((0, "serial_send", packet))
                self.__valve_control_in_progress  = True
                self.__valve_control_target       = value
                self.__valve_control_start_time   = utime.time()
                log.info("Valve control started: target=%d%%" % value)
                self.__refresh_valve_display()
                response = {"status": "OK"}
            else:
                if value is not None:
                    log.error("setState rejected: %d out of range 0-100" % value)
                response = {"status": "FAILURE", "error": "params must be 0-100"}
        else:
            response = {"status": "FAILURE"}

        link.send_rpc_reply(ujson.dumps(response), request_id)
        self.__business_queue.put((0, "loc_report"))

    def __read_modbus_data(self):
        global PH_SENSOR_VALUE, TDS_VALUE, CHLORINE_VAL, NITRATE_VAL, ANALOG_VAL, BATT_CAP, BATT_VOLT
        global ANALOG_ERR, PH_ERR, TDS_ERR, CHLORINE_ERR, NITRATE_ERR, BATT_CAP_ERR, BATT_VOLT_ERR
        global ANALOG_CHANNELS
        global BATT_CURR, BATT_CURR_ERR

        if self.__valve_control_in_progress:
            log.debug("Modbus read skipped - valve control in progress")
            return

        if not self.__modbus:
            log.error("Modbus not initialized")
            return

        log.debug("Starting Modbus data read cycle")
        try:
            req = self.__modbus.build_read_input_registers(0x01, 0x0000, 8)
            data = self.__modbus.send_modbus_request(req, expected_len=21)
            if data:
                status, values = self.__modbus.extract_analog_values(data, 21)
                if status == 0:
                    ANALOG_VAL      = (values[7] - 4000) * 0.625 / 1000
                    ANALOG_CHANNELS = values
                    ANALOG_ERR      = False
                    log.debug("Analog values: %s" % values)
                else:
                    ANALOG_ERR = True
                    log.error("Failed to extract analog values, status: %d" % status)
            else:
                ANALOG_ERR = True
                log.error("No valid response for analog values")

            if self.valve_changed_flag:
                return
            utime.sleep_ms(1)

            req = self.__modbus.build_read_holding_registers(0x05, 0x0002, 1)
            data = self.__modbus.send_modbus_request(req, expected_len=7)
            if data:
                status, value = self.__modbus.extract_ph_value(data, 7)
                if status == 0:
                    PH_SENSOR_VALUE = value
                    PH_ERR = False
                else:
                    PH_ERR = True
                    log.error("Failed to extract pH, status: %d" % status)
            else:
                PH_ERR = True

            if self.valve_changed_flag:
                return
            utime.sleep_ms(1)

            req = self.__modbus.build_read_holding_registers(0x04, 0x0008, 2)
            data = self.__modbus.send_modbus_request(req, expected_len=9)
            if data:
                status, value = self.__modbus.extract_tds_value(data, 9)
                if status == 0:
                    TDS_VALUE = value
                    TDS_ERR = False
                else:
                    TDS_ERR = True
            else:
                TDS_ERR = True

            if self.valve_changed_flag:
                return
            utime.sleep_ms(1)

            req = self.__modbus.build_read_holding_registers(0x07, 0x0000, 1)
            data = self.__modbus.send_modbus_request(req, expected_len=7)
            if data:
                status, value = self.__modbus.extract_chlorine_value(data, 7)
                if status == 0:
                    CHLORINE_VAL = value
                    CHLORINE_ERR = False
                else:
                    CHLORINE_ERR = True
            else:
                CHLORINE_ERR = True

            if self.valve_changed_flag:
                return
            utime.sleep_ms(1)

            req = self.__modbus.build_read_holding_registers(0x09, 0x0001, 1)
            data = self.__modbus.send_modbus_request(req, expected_len=7)
            if data:
                status, value = self.__modbus.extract_nitrate_value(data, 7)
                if status == 0:
                    NITRATE_VAL = value
                    NITRATE_ERR = False
                else:
                    NITRATE_ERR = True
            else:
                NITRATE_ERR = True

            if self.valve_changed_flag:
                return
            utime.sleep_ms(1)

            req = self.__modbus.build_read_input_registers(0x0A, 0x3045, 1)
            data = self.__modbus.send_modbus_request(req, expected_len=7)
            if data:
                status, value = self.__modbus.extract_batt_capacity(data, 7)
                if status == 0:
                    BATT_CAP     = value
                    BATT_CAP_ERR = False
                else:
                    BATT_CAP_ERR = True
            else:
                BATT_CAP_ERR = True

            if self.valve_changed_flag:
                return
            utime.sleep_ms(1)

            req = self.__modbus.build_read_input_registers(0x0A, 0x3046, 1)
            data = self.__modbus.send_modbus_request(req, expected_len=7)
            if data:
                status, value = self.__modbus.extract_batt_voltage(data, 7)
                if status == 0:
                    BATT_VOLT     = value
                    BATT_VOLT_ERR = False
                else:
                    BATT_VOLT_ERR = True
            else:
                BATT_VOLT_ERR = True

            req = self.__modbus.build_read_input_registers(0x0A, 0x304B, 1)
            data = self.__modbus.send_modbus_request(req, expected_len=7)
            if data:
                status, value = self.__modbus.extract_batt_voltage(data, 7)
                if status == 0:
                    BATT_CURR     = value / 100
                    BATT_CURR_ERR = False
                else:
                    BATT_CURR_ERR = True
            else:
                BATT_CURR_ERR = True

        except Exception as e:
            log.error("Error reading Modbus data: %s" % str(e))

    def __serial_callback_handler(self, para):
        try:
            if para[0] == 0:
                data_len = self.__serial.any()
                if data_len > 0:
                    data = self.__serial.read(data_len)
                    if data:
                        self.__serial_last_rx_time = utime.time()
                        send_flow_ack = False
                        pending_valve_packet = None
                        with self.__serial_lock:
                            self.__serial_buffer.extend(data)
                            if len(self.__serial_buffer) > 1024:
                                log.error("Serial buffer overflow, clearing")
                                self.__serial_buffer = bytearray()
                                return

                            while len(self.__serial_buffer) >= 18:
                                packet_bytes = self.__serial_buffer[:18]
                                try:
                                    reconstructed_packet = CANPacket.from_bytes(packet_bytes)
                                    # Any decoded packet is proof-of-life for MSPM0.
                                    self.__mspm0_last_packet_time = utime.time()
                                    if not self.__mspm0_connected:
                                        self.__mspm0_connected = True
                                        self.__business_queue.put((0, "loc_report"))
                                    self.__business_queue.put((0, "serial_data", reconstructed_packet))
                                    self.__serial_consecutive_errors = 0
                                    # Flow packet: ack MSPM0 immediately (below) to feed its comms watchdog.
                                    if reconstructed_packet.can_cmd == 0xAA10:
                                        send_flow_ack = True
                                    elif reconstructed_packet.can_cmd == 0xAA01:
                                        pending_valve_packet = reconstructed_packet
                                except ValueError as ve:
                                    log.error("Invalid CAN packet: %s" % str(ve))
                                    self.__serial_consecutive_errors += 1
                                    if self.__serial_consecutive_errors >= 5:
                                        log.error("Too many packet errors, triggering recovery")
                                        _thread.start_new_thread(self.__serial_recover, ())
                                        self.__serial_consecutive_errors = 0
                                        return
                                except Exception as pe:
                                    log.error("Packet decode error: %s" % str(pe))
                                finally:
                                    self.__serial_buffer = self.__serial_buffer[18:]
                        if send_flow_ack:
                            self.__send_flow_ack()
                        if pending_valve_packet is not None:
                            # Straight off the UART RX callback - no business queue delay.
                            self.__update_valve_display_immediate(pending_valve_packet)
        except Exception as e:
            log.error("Error in serial callback: %s" % str(e))
            import sys
            sys.print_exception(e)
            try:
                with self.__serial_lock:
                    self.__serial_buffer = bytearray()
            except:
                pass

    def __serial_start(self):
        if self.__serial:
            try:
                res = self.__serial.set_callback(self.__serial_callback_handler)
                if res != 0:
                    log.error("Failed to set UART callback: %d" % res)
                else:
                    log.debug("Serial callback registered")
            except Exception as e:
                log.error("Failed to register serial callback: %s" % str(e))

    def __serial_stop(self):
        self.__serial_tid = None
        if self.__serial:
            try:
                self.__serial.set_callback(None)
                self.__serial.close()
            except Exception as e:
                log.error("Error closing serial: %s" % str(e))
        with self.__serial_lock:
            self.__serial_buffer = bytearray()

    def __serial_recover(self):
        if self.__serial_recovery_in_progress:
            return
        try:
            self.__serial_recovery_in_progress = True
            if self.__serial:
                try:
                    self.__serial.set_callback(None)
                    utime.sleep_ms(100)
                    self.__serial.close()
                    utime.sleep_ms(100)
                except Exception as e:
                    log.error("Error during serial close: %s" % str(e))
            with self.__serial_lock:
                self.__serial_buffer = bytearray()
            try:
                self.__serial = UART(UART.UART2, 115200, 8, 0, 1, 0)
                log.debug("Serial UART2 reinitialized")
            except Exception as e:
                log.error("Failed to reinitialize UART: %s" % str(e))
                self.__serial_recovery_in_progress = False
                return
            self.__serial_start()
            self.__serial_last_rx_time       = utime.time()
            self.__serial_consecutive_errors = 0
            log.info("Serial recovery completed")
        except Exception as e:
            log.error("Serial recovery failed: %s" % str(e))
        finally:
            self.__serial_recovery_in_progress = False

    def __serial_watchdog_check(self, args):
        try:
            current_time = utime.time()
            if self.__serial_last_rx_time == 0:
                self.__serial_last_rx_time = current_time
                return
            elapsed = current_time - self.__serial_last_rx_time
            if elapsed > 30:
                log.warning("Serial watchdog: No data for %d seconds" % elapsed)
                self.__serial_recover()
            # Reuses this 15s timer for MSPM0 status + board heartbeat, no extra timer.
            self.__refresh_mspm0_connection(current_time)
            self.__touch_board_heartbeat()
        except Exception as e:
            log.error("Serial watchdog check error: %s" % str(e))

    def __memory_check(self, args):
        try:
            gc.collect()
            current_free = gc.mem_free()
            mem_diff     = current_free - self.__last_free_mem
            if mem_diff < -10000:
                log.warning("Memory decreased: %d bytes (free: %d)" % (mem_diff, current_free))
            else:
                log.debug("Memory check: free=%d bytes (diff: %+d)" % (current_free, mem_diff))
            if current_free < 50000:
                log.error("CRITICAL: Low memory! Only %d bytes free" % current_free)
                gc.collect()
                current_free = gc.mem_free()
                if current_free < 30000:
                    log.error("FATAL: Memory critically low!")
            self.__last_free_mem = current_free
        except Exception as e:
            log.error("Memory check error: %s" % str(e))

    def __update_learn_session(self, raw_value):
        # Must be called with __valve_lock held. Session-only - never writes min_value/max_value/min_max.json.
        range_changed = False
        if self.__learn_session_min is None or raw_value < self.__learn_session_min:
            self.__learn_session_min = raw_value
            range_changed = True
        if self.__learn_session_max is None or raw_value > self.__learn_session_max:
            self.__learn_session_max = raw_value
            range_changed = True
        self.__learn_session_samples += 1

        return range_changed

    def __process_serial_data(self, can_data):
        global LEARN_MODE
        try:
            if not can_data or not hasattr(can_data, 'data'):
                log.error("Invalid CAN packet received")
                return

            data_bytes            = bytes(can_data.data)
            integer_little_endian = int.from_bytes(data_bytes, 'little')

            log.debug("CAN packet: cmd=0x%X raw=%d" % (can_data.can_cmd, integer_little_endian))

            changed = False
            current_status = 0
            if can_data.can_cmd == 0xBB01:
                if LEARN_MODE == 1:
                    with self.__valve_lock:
                        self.__update_learn_session(integer_little_endian)
                    log.debug("Learn mode sample (BB01): %d" % integer_little_endian)
                else:
                    # Ignore MSPM0's own boot-time report within the boot-settle window.
                    if (utime.time() - self.__boot_settle_time < BOOT_SETTLE_SEC) or (not self.__boot_bb01_ignored):
                        self.__boot_bb01_ignored = True
                        log.warning(
                            "Ignoring BB01 (min=%d) received %ds after boot - "
                            "within boot-settle window" % (
                                integer_little_endian, utime.time() - self.__boot_settle_time))
                    else:
                        with self.__valve_lock:
                            self.min_value = integer_little_endian
                        log.debug("Bottom value updated: %d" % self.min_value)
                        self.save_min_max(force=True)

            elif can_data.can_cmd == 0xBB02:
                if LEARN_MODE == 1:
                    with self.__valve_lock:
                        self.__update_learn_session(integer_little_endian)
                    log.debug("Learn mode sample (BB02): %d" % integer_little_endian)
                else:
                    if (utime.time() - self.__boot_settle_time < BOOT_SETTLE_SEC) or (not self.__boot_bb02_ignored):
                        self.__boot_bb02_ignored = True
                        log.warning(
                            "Ignoring BB02 (max=%d) received %ds after boot - "
                            "within boot-settle window" % (
                                integer_little_endian, utime.time() - self.__boot_settle_time))
                    else:
                        with self.__valve_lock:
                            self.max_value = integer_little_endian
                        log.debug("Top value updated: %d" % self.max_value)
                        self.save_min_max(force=True)

            elif can_data.can_cmd == 0xAA01:
                if LEARN_MODE == 1:
                    with self.__valve_lock:
                        self.cur_value = integer_little_endian
                        self.__update_learn_session(integer_little_endian)
                else:
                    with self.__valve_lock:
                        self.cur_value = integer_little_endian
                        try:
                            if self.max_value > self.min_value and self.max_value > 0:
                                clamped    = max(self.min_value, min(integer_little_endian, self.max_value))
                                percentage = (clamped - self.min_value) * 100.0 / (self.max_value - self.min_value)
                                percentage = max(0, min(100, percentage))
                            else:
                                percentage = 0
                        except Exception as calc_err:
                            log.error("Percentage calculation error: %s" % str(calc_err))
                            percentage = 0

                        global VALVE_STATUS
                        current_status = int(percentage)

                        if self.__valve_control_in_progress:
                            target_reached  = abs(current_status - self.__valve_control_target) <= 5
                            time_elapsed    = utime.time() - self.__valve_control_start_time
                            timeout_exceeded = time_elapsed > 60
                            if target_reached or timeout_exceeded:
                                self.__valve_control_in_progress = False
                                if target_reached:
                                    log.info("Valve reached %d%% (target %d%%)" % (
                                        current_status, self.__valve_control_target))
                                else:
                                    log.warning("Valve timeout at %d%% after %ds" % (
                                        current_status, int(time_elapsed)))
                                self.__business_queue.put((0, "loc_report"))

                        changed = abs(current_status - self.previous_valve_status) > 1
                        if changed:
                            VALVE_STATUS = current_status
                            self.previous_valve_status = current_status
                            self.valve_changed_flag    = True

                            if self.__valve_control_in_progress:
                                if current_status % 10 == 0 or abs(current_status - self.__valve_control_target) <= 5:
                                    self.__business_queue.put((0, "loc_report"))
                            else:
                                self.__business_queue.put((0, "loc_report"))
                        else:
                            VALVE_STATUS = current_status
                            if current_status != self.previous_valve_status:
                                self.previous_valve_status = current_status

                    if changed:
                        if not self.__valve_control_in_progress or current_status % 10 == 0:
                            self.save_min_max()

            elif can_data.can_cmd == 0xAA10:
                self.__last_raw_flow_value = integer_little_endian

                # Only update/log while valve is open, at most once a minute.
                global FLOW_METER_VALUE
                valve_open = VALVE_STATUS > 0
                if valve_open:
                    now = utime.time()
                    just_opened = not self.__flow_meter_valve_was_open
                    if just_opened or (now - self.__last_flow_update_time) >= 60:
                        with self.__flow_lock:
                            FLOW_METER_VALUE = integer_little_endian + self.__flow_base
                        self.__last_flow_update_time = now
                        log.info("Flow Meter Value: %d (raw=%d offset=%d VALVE_STATUS=%d%%)" % (
                            FLOW_METER_VALUE, integer_little_endian, self.__flow_base, VALVE_STATUS))
                    self.__flow_meter_valve_was_open = True
                    if self.__leak_samples:
                        self.__leak_samples = []
                    if self.__leak_alert_active:
                        self.__clear_leak_alert("valve opened")
                else:
                    if self.__flow_meter_valve_was_open:
                        log.info("Valve closed (VALVE_STATUS=%d%%) - flow meter updates paused, holding last value %d" % (VALVE_STATUS, FLOW_METER_VALUE))
                    self.__flow_meter_valve_was_open = False
                    self.__check_leak_detection(integer_little_endian)
                # BBFF ack is sent immediately from __serial_callback_handler, not here.

            elif can_data.can_cmd == 0xAA20:
                new_learn_mode = int(integer_little_endian)

                if new_learn_mode == 1 and self.__previous_learn_mode == 0:
                    # Fresh session - clear running min/max.
                    with self.__valve_lock:
                        self.__learn_session_min = None
                        self.__learn_session_max = None
                        self.__learn_session_samples = 0
                    log.info("Entering learn mode - watching for manual valve movement")

                    LEARN_MODE = new_learn_mode
                    self.__previous_learn_mode = new_learn_mode
                    self.__refresh_learn_display()
                    return

                if self.__previous_learn_mode == 1 and new_learn_mode == 0:
                    # Snapshot the learned range.
                    with self.__valve_lock:
                        session_min     = self.__learn_session_min
                        session_max     = self.__learn_session_max
                        session_samples = self.__learn_session_samples
                        learned_ok = (session_min is not None and session_max is not None
                                      and session_max > session_min)
                        if learned_ok:
                            self.min_value = session_min
                            self.max_value = session_max
                        self.__learn_last_min     = session_min
                        self.__learn_last_max     = session_max
                        self.__learn_last_samples = session_samples
                        self.__learn_last_ok      = learned_ok

                    if learned_ok:
                        self.save_min_max(force=True)
                        self.__send_valve_min_max_to_msp(session_min, session_max)
                        log.info("Learn mode committed: min=%d max=%d (%d samples) - synced to MSPM0" % (
                            session_min, session_max, session_samples))
                    else:
                        log.warning(
                            "Learn mode INCOMPLETE: min=%s max=%s (%d samples) - "
                            "previous min/max left unchanged" % (
                                session_min, session_max, session_samples))

                    # Force a fresh comparison on the next real AA01.
                    self.__last_immediate_valve_pct = None

                    log.info("Exiting learn mode")

                    LEARN_MODE = new_learn_mode
                    self.__previous_learn_mode = new_learn_mode
                    log.debug("Learn mode: %d" % LEARN_MODE)

                    self.__refresh_learn_exit_display()

        except Exception as e:
            log.error("Error processing serial data: %s" % str(e))

    def __send_serial_data(self, data):
        try:
            if self.__serial:
                raw = data.to_bytes()
                with self.__serial_tx_lock:
                    self.__serial.write(raw)
                log.debug("Sent serial data: %d bytes" % len(raw))
        except Exception as e:
            log.error("Error sending serial data: %s" % str(e))

    def __send_flow_ack(self):
        try:
            if self.__serial:
                with self.__serial_tx_lock:
                    self.__serial.write(self.__flow_ack_bytes)
        except Exception as e:
            log.error("Error sending flow ack: %s" % str(e))

    def save_min_max(self, force=False):
        with self.__file_lock:
            try:
                current_time = utime.time()
                if not force and (current_time - self.__last_save_time) < 10:
                    return
                with self.__valve_lock:
                    data = {
                        'min_value': self.min_value,
                        'max_value': self.max_value,
                        'cur_value': self.cur_value
                    }
                import uos
                temp_path  = '/usr/min_max.tmp'
                final_path = '/usr/min_max.json'
                try:
                    uos.remove(temp_path)
                except:
                    pass
                try:
                    try:
                        uos.remove(final_path)
                    except:
                        pass
                    with open(temp_path, 'w') as f:
                        ujson.dump(data, f)
                    uos.rename(temp_path, final_path)
                    self.__last_save_time = current_time
                    log.debug("Saved min_max.json: min=%d max=%d cur=%d" % (
                        data['min_value'], data['max_value'], data['cur_value']))
                except OSError as e:
                    if e.args[0] == 28:
                        try:
                            uos.remove(temp_path)
                        except:
                            pass
                        with open(final_path, 'w') as f:
                            ujson.dump(data, f)
                        self.__last_save_time = current_time
                    else:
                        raise
            except Exception as e:
                log.error("Failed to save min_max.json: %s" % str(e))

    def load_min_max(self):
        need_save = False
        with self.__file_lock:
            try:
                with open('/usr/min_max.json', 'r') as f:
                    data = ujson.load(f)
                with self.__valve_lock:
                    self.min_value = data.get('min_value', 25000)
                    self.max_value = data.get('max_value', 35000)
                    self.cur_value = data.get('cur_value', 30000)
                    if self.cur_value < self.min_value:
                        self.cur_value = 30000
                    if self.max_value > self.min_value:
                        self.previous_valve_status = int(
                            (self.cur_value - self.min_value) * 100 / (self.max_value - self.min_value))
                    else:
                        self.previous_valve_status = 0
                log.debug("Loaded min_max: min=%d max=%d cur=%d valve=%d%%" % (
                    self.min_value, self.max_value, self.cur_value, self.previous_valve_status))
            except Exception as e:
                log.debug("Failed to load min_max.json: %s, using defaults" % str(e))
                with self.__valve_lock:
                    self.min_value             = 25000
                    self.max_value             = 35000
                    self.cur_value             = 30000
                    self.previous_valve_status = 0
                need_save = True
        # Persist AFTER releasing __file_lock - save_min_max() re-acquires it (non-reentrant).
        if need_save:
            self.save_min_max()

    def __load_flow_base(self):
        # Loads the persisted calibration offset. FLOW,<value> SMS sets it - see __update_flow_counter.
        try:
            with open('/usr/flow_base.json', 'r') as f:
                data = ujson.load(f)
            with self.__flow_lock:
                self.__flow_base = data.get('flow_base', 0)
            self.__flow_base_loaded = True
            log.info("Loaded flow meter calibration offset: %d" % self.__flow_base)
        except Exception:
            with self.__flow_lock:
                self.__flow_base = 0
            self.__flow_base_loaded = True
            log.debug("No flow_base.json found, flow calibration offset is 0")
        global FLOW_METER_VALUE
        with self.__flow_lock:
            FLOW_METER_VALUE = self.__flow_base

    def __save_flow_base(self):
        try:
            import uos
            temp  = '/usr/flow_base.tmp'
            final = '/usr/flow_base.json'
            with self.__flow_lock:
                flow_base_to_save = self.__flow_base
            try:
                uos.remove(temp)
            except:
                pass
            with open(temp, 'w') as f:
                ujson.dump({'flow_base': flow_base_to_save}, f)
            try:
                uos.remove(final)
            except:
                pass
            uos.rename(temp, final)
            log.debug("Saved flow calibration offset: %d" % flow_base_to_save)
        except OSError as e:
            if e.args[0] == 28:
                log.error("Filesystem full, falling back to direct write for flow_base.json")
                try:
                    with open('/usr/flow_base.json', 'w') as f:
                        ujson.dump({'flow_base': flow_base_to_save}, f)
                    log.warning("flow_base.json direct write succeeded (no atomic safety)")
                except Exception as inner_e:
                    log.error("Direct write of flow_base.json also failed: %s" % str(inner_e))
            else:
                log.error("Failed to save flow_base.json: %s" % str(e))
        except Exception as e:
            log.error("Failed to save flow_base.json: %s" % str(e))

    def __update_flow_counter(self, value):
        # FLOW,<value> SMS: calibrate FLOW_METER_VALUE to the physical meter's manual reading now.
        global FLOW_METER_VALUE
        with self.__flow_lock:
            self.__flow_base = value - self.__last_raw_flow_value
            FLOW_METER_VALUE = value
            raw_at_calibration = self.__last_raw_flow_value
            offset_saved = self.__flow_base
        self.__save_flow_base()
        log.info("Flow meter calibrated via SMS: set to %d (raw=%d, new offset=%d)" % (
            value, raw_at_calibration, offset_saved))
        self.__business_queue.put((0, "loc_report"))

    def __apply_timer_config(self, cloud_time_sec, sensor_read_sec):
        # SETTIMER,... SMS. Applies both live - re-arms the RTC alarm and restarts the modbus timer.
        self.__cloud_time_sec = cloud_time_sec
        self.__set_rtc(cloud_time_sec, self.loc_report)

        self.__modbus_interval_ms = sensor_read_sec * 1000
        if self.__modbus:
            self.__modbus_timer.stop()
            self.__modbus_timer.start(self.__modbus_interval_ms, 1, self.modbus_read_callback)

        log.info("Timer config applied: cloud=%ds sensor=%ds" % (cloud_time_sec, sensor_read_sec))

    def __send_valve_min_max_to_msp(self, min_val, max_val):
        # Syncs the learned range to MSPM0's own calibration.
        try:
            min_val = int(min_val)
            max_val = int(max_val)

            if max_val <= min_val:
                log.warning("Not sending invalid valve range: min=%d max=%d" % (
                    min_val, max_val))
                return False

            min_data_bytes = min_val.to_bytes(8, 'little')
            packet_min = CANPacket(
                interface_type=0x01,
                can_cmd=0xBB01,
                data=list(min_data_bytes),
                seq_id=1234,
                crc_16=1234
            )

            max_data_bytes = max_val.to_bytes(8, 'little')
            packet_max = CANPacket(
                interface_type=0x01,
                can_cmd=0xBB02,
                data=list(max_data_bytes),
                seq_id=1234,
                crc_16=1234
            )

            self.__business_queue.put((0, "serial_send", packet_min))
            utime.sleep(1)
            self.__business_queue.put((0, "serial_send", packet_max))

            log.info("Synced valve range to MSPM0: min=%d max=%d" % (
                min_val, max_val))
            return True
        except Exception as e:
            log.error("Failed to sync valve min/max to MSPM0: %s" % str(e))
            return False

    def send_min_max_on_boot(self):
        try:
            with self.__valve_lock:
                min_val = self.min_value
                max_val = self.max_value
                cur_val = self.cur_value
            min_data_bytes = min_val.to_bytes(8, 'little')
            packet_min = CANPacket(interface_type=0x01, can_cmd=0xBB01,
                                   data=list(min_data_bytes), seq_id=1234, crc_16=1234)
            self.__business_queue.put((0, "serial_send", packet_min))
            utime.sleep(1)
            max_data_bytes = max_val.to_bytes(8, 'little')
            packet_max = CANPacket(interface_type=0x01, can_cmd=0xBB02,
                                   data=list(max_data_bytes), seq_id=1234, crc_16=1234)
            self.__business_queue.put((0, "serial_send", packet_max))
            utime.sleep(1)
            current_bytes = cur_val.to_bytes(8, 'little')
            packet_cur = CANPacket(interface_type=0x01, can_cmd=0xAA01,
                                   data=list(current_bytes), seq_id=1234, crc_16=1234)
            self.__business_queue.put((0, "serial_send", packet_cur))
            log.debug("Sent min/max/cur on boot: min=%d max=%d cur=%d" % (min_val, max_val, cur_val))
        except Exception as e:
            log.error("Error sending min_max on boot: %s" % str(e))

    def __format_dhms(self, seconds):
        # days:hours:minutes:seconds, zero-padded.
        try:
            seconds = int(seconds)
        except Exception:
            seconds = 0
        if seconds < 0:
            seconds = 0
        days = seconds // 86400
        hours = (seconds % 86400) // 3600
        minutes = (seconds % 3600) // 60
        secs = seconds % 60
        return "%02d:%02d:%02d:%02d" % (days, hours, minutes, secs)

    def __board_uptime_sec(self):
        # Seconds since boot, from a monotonic tick counter (not utime.time(), which can jump).
        try:
            return int(utime.ticks_diff(utime.ticks_ms(), self.__boot_ticks_ms) / 1000)
        except Exception:
            return 0

    def __connection_label(self, connected):
        return "Connected" if connected else "Not Connected"

    def __mqtt_is_up(self):
        s1 = self.__server is not None and self.__server.status
        s2 = self.__server2 is not None and self.__server2.status
        return bool(s1 or s2)

    def __refresh_mspm0_connection(self, now=None):
        # Connected iff a packet was decoded within MSPM0_OFFLINE_SEC. Called from the watchdog + loc_report only.
        if now is None:
            now = utime.time()
        if self.__mspm0_last_packet_time == 0:
            connected = False
        else:
            age = int(now - self.__mspm0_last_packet_time)
            connected = age <= MSPM0_OFFLINE_SEC
        self.__mspm0_connected = connected
        return connected

    def __board_health_telemetry(self, mqtt_up):
        # Board/MSPM0 status + uptime/downtime + reboot count, folded into telemetry.
        mspm0_up = self.__refresh_mspm0_connection()
        uptime = self.__board_uptime_sec()
        last_dt = int(self.__board_last_downtime_sec)
        return {
            "Brd_Conn": self.__connection_label(mqtt_up),
            "MSPM0 Status": self.__connection_label(mspm0_up),
            "Brd_Uptime": self.__format_dhms(uptime),
            "Brd_Downtime": self.__format_dhms(last_dt),
            "EC200_reboot_cnt": int(self.__board_reboot_count),
        }

    def __default_board_health(self):
        return {
            "last_seen_epoch": 0,
            "total_uptime_sec": 0,
            "total_downtime_sec": 0,
            "last_downtime_sec": 0,
            "EC200_reboot_cnt": 0,
        }

    def __write_board_health(self, data):
        # Same atomic temp-then-rename pattern as save_min_max()/__save_flow_base().
        import uos
        try:
            uos.remove(BOARD_HEALTH_TMP_PATH)
        except:
            pass
        try:
            try:
                uos.remove(BOARD_HEALTH_PATH)
            except:
                pass
            with open(BOARD_HEALTH_TMP_PATH, "w") as f:
                ujson.dump(data, f)
            uos.rename(BOARD_HEALTH_TMP_PATH, BOARD_HEALTH_PATH)
        except OSError as e:
            if e.args[0] == 28:
                try:
                    uos.remove(BOARD_HEALTH_TMP_PATH)
                except:
                    pass
                with open(BOARD_HEALTH_PATH, "w") as f:
                    ujson.dump(data, f)
            else:
                raise

    def __read_board_health(self):
        data = self.__default_board_health()
        try:
            with open(BOARD_HEALTH_PATH, "r") as f:
                loaded = ujson.load(f)
            if isinstance(loaded, dict):
                data.update(loaded)
        except Exception:
            pass
        return data

    def __snapshot_board_health(self):
        return {
            "last_seen_epoch": int(self.__board_last_seen_epoch),
            "total_uptime_sec": int(self.__board_total_uptime_sec + self.__board_uptime_sec()),
            "total_downtime_sec": int(self.__board_total_downtime_sec),
            "last_downtime_sec": int(self.__board_last_downtime_sec),
            "EC200_reboot_cnt": int(self.__board_reboot_count),
        }

    def __load_board_health(self):
        # Boot-once: reads persisted health, computes downtime since last seen, bumps reboot count.
        # "EC200_reboot_cnt" is the only key used, on both read and write.
        with self.__file_lock:
            health = self.__read_board_health()
            self.__board_total_uptime_sec = int(health.get("total_uptime_sec", 0))
            self.__board_reboot_count = int(health.get("EC200_reboot_cnt", 0)) + 1

            last_seen = int(health.get("last_seen_epoch", 0))
            now = int(utime.time())
            downtime = 0
            if last_seen > 100000 and now > last_seen:
                downtime = now - last_seen
                if downtime > 365 * 24 * 3600:
                    # RTC likely unset last time - 0 is safer than a bogus multi-year downtime.
                    downtime = 0
            self.__board_last_downtime_sec = downtime
            self.__board_total_downtime_sec = int(health.get("total_downtime_sec", 0)) + downtime
            self.__board_last_seen_epoch = now

            try:
                self.__write_board_health(self.__snapshot_board_health())
                self.__last_health_save_time = utime.time()
            except Exception as e:
                log.error("Failed to persist board health at boot: %s" % str(e))
            log.info(
                "Board health: downtime=%ds total_uptime=%ds reboots=%d" % (
                    self.__board_last_downtime_sec, self.__board_total_uptime_sec,
                    self.__board_reboot_count))

    def __touch_board_heartbeat(self):
        # Re-persists last_seen_epoch. Called from the watchdog + loc_report, no timer of its own.
        # Writes at most every 10s, or on a connection-label change, to spare the flash.
        now = utime.time()
        self.__board_last_seen_epoch = int(now)
        board_conn = self.__connection_label(self.__mqtt_is_up())
        mspm0_conn = self.__connection_label(self.__mspm0_connected)
        conn_changed = (
            board_conn != self.__last_persisted_board_connection or
            mspm0_conn != self.__last_persisted_mspm0_connection
        )
        if (not conn_changed) and (now - self.__last_health_save_time) < 10:
            return
        with self.__file_lock:
            try:
                self.__write_board_health(self.__snapshot_board_health())
                self.__last_health_save_time = now
                self.__last_persisted_board_connection = board_conn
                self.__last_persisted_mspm0_connection = mspm0_conn
            except Exception as e:
                log.error("Failed to save board health: %s" % str(e))

    def __power_restart(self):
        if self.__reset_tag == 1:
            return
        self.__reset_tag = 1
        count = 0
        while (self.__business_queue.size() > 0 or self.__business_tag == 1) and count < 30:
            count += 1
            utime.sleep(1)
        Power.powerRestart()

    def __get_datetime_string(self):
        try:
            t = utime.localtime()
            return "{:02d}/{:02d}/{:02d} {:02d}:{:02d}:{:02d}".format(
                t[2], t[1], t[0] % 100, t[3], t[4], t[5])
        except Exception:
            return "01/01/25 00:00:00"

    def __display_page_1(self):
        global IMEI
        try:
            if not self.__lcd:
                return
            self.__lcd.display_string("---WATER QUALITY---", 1)
            self.__lcd.display_string("-MONITORING SYSTEM-", 2)
            self.__lcd.display_string("ID :{}".format(IMEI[:20]), 3)
            self.__lcd.display_string(self.__get_datetime_string()[:20], 4)
        except Exception as e:
            log.error("Page 1 error: %s" % str(e))

    def __display_page_2(self):
        try:
            global PH_SENSOR_VALUE, TDS_VALUE, CHLORINE_VAL, NITRATE_VAL
            global PH_ERR, TDS_ERR, CHLORINE_ERR, NITRATE_ERR
            if self.__lcd:
                self.__lcd.display_string("-QUALITY PARAMETERS-", 1)
                tds_display = "ERR" if TDS_ERR    else "{}mg/L".format(int(TDS_VALUE))
                ni_display  = "ERR" if NITRATE_ERR else "{}mg/L".format(int(NITRATE_VAL))
                cl_display  = "ERR" if CHLORINE_ERR else "{:.2f}".format(float(CHLORINE_VAL))
                ph_display  = "ERR" if PH_ERR      else "{:.1f}".format(float(PH_SENSOR_VALUE))
                self.__lcd.display_string("TDS :{}".format(tds_display)[:20], 2)
                self.__lcd.display_string("NI  :{}".format(ni_display)[:20], 3)
                self.__lcd.display_string("CL  :{}   PH:{}".format(cl_display, ph_display)[:20], 4)
        except Exception as e:
            log.error("Page 2 error: %s" % str(e))

    def __display_page_3(self):
        try:
            global BATT_CAP, BATT_VOLT, BATT_CAP_ERR, BATT_VOLT_ERR
            if self.__lcd:
                self.__lcd.display_string("--POWER PARAMETERS--", 1)
                soc_display  = "ERR" if BATT_CAP_ERR  else "{}%".format(int(BATT_CAP))
                volt_display = "ERR" if BATT_VOLT_ERR else "{:.2f}V".format(BATT_VOLT)
                curr_display = "ERR" if BATT_VOLT_ERR else "{:.2f}A".format(BATT_CURR)
                self.__lcd.display_string("BAT SOC : {}".format(soc_display)[:20], 2)
                self.__lcd.display_string("BAT VOL : {}".format(volt_display)[:20], 3)
                self.__lcd.display_string("BAT CUR : {}".format(curr_display)[:20], 4)
        except Exception as e:
            log.error("Page 3 error: %s" % str(e))

    def __display_page_4(self):
        try:
            global VALVE_STATUS, ANALOG_VAL, ANALOG_ERR
            if self.__lcd:
                valve_pct     = int(VALVE_STATUS)
                status        = "OPEN " if valve_pct > 0 else "CLOSE"
                press_display = "ERR" if ANALOG_ERR else "{:.2f}BAR".format(ANALOG_VAL)
                self.__lcd.display_string("--Valve Params--", 1)
                self.__lcd.display_string("Status : {}".format(status)[:20], 2)
                self.__lcd.display_string("Level  : {}%".format(valve_pct)[:20], 3)
                self.__lcd.display_string("Press  : {}".format(press_display)[:20], 4)
        except Exception as e:
            log.error("Page 4 error: %s" % str(e))

    def __display_page_5(self):
        try:
            global LOCATION_VALUE, SERVER_STATUS
            if self.__lcd:
                self.__lcd.display_string("--NETWORK STATUS--", 1)
                self.__lcd.display_string("Srv:{}".format(SERVER_STATUS)[:20], 2)
                if LOCATION_VALUE:
                    parts = LOCATION_VALUE.split(',')
                    if len(parts) >= 2:
                        self.__lcd.display_string(("Lt:" + parts[0].strip()[:17])[:20], 3)
                        self.__lcd.display_string(("Ln:" + parts[1].strip()[:17])[:20], 4)
                    else:
                        self.__lcd.display_string("GPS: No Fix", 3)
                        self.__lcd.display_string("", 4)
                else:
                    self.__lcd.display_string("GPS: Searching...", 3)
                    self.__lcd.display_string("", 4)
        except Exception as e:
            log.error("Page 5 error: %s" % str(e))

    def __display_page_learn(self):
        # Shown for the whole learn-mode duration, redrawn on the 5s display cycle.
        try:
            if self.__lcd:
                with self.__valve_lock:
                    session_min     = self.__learn_session_min
                    session_max     = self.__learn_session_max
                    session_samples = self.__learn_session_samples
                low_str  = "{}".format(session_min) if session_min is not None else "---"
                high_str = "{}".format(session_max) if session_max is not None else "---"
                self.__lcd.display_string("-VALVE LEARNING MODE-", 1)
                self.__lcd.display_string("Move valve fully", 2)
                self.__lcd.display_string("open and closed", 3)
                self.__lcd.display_string("Lo:{} Hi:{} n={}".format(
                    low_str, high_str, session_samples)[:20], 4)
        except Exception as e:
            log.error("Learning mode page error: %s" % str(e))

    def __display_learn_exit_message(self):
        # Runs once, right after learn mode exits (1 -> 0). Shows the session's actual sensed range.
        try:
            if self.__lcd:
                with self.__valve_lock:
                    min_val = self.__learn_last_min
                    max_val = self.__learn_last_max
                    samples = self.__learn_last_samples
                    ok      = self.__learn_last_ok

                low_str  = "{}".format(min_val) if min_val is not None else "NONE"
                high_str = "{}".format(max_val) if max_val is not None else "NONE"

                self.__lcd.display_string(
                    "LEARNING COMPLETE  " if ok else "LEARNING INCOMPLETE", 1)
                self.__lcd.display_string("Samples: {}".format(samples)[:20], 2)
                self.__lcd.display_string(
                    "LOW :{}{}".format(low_str, " OK" if ok else "")[:20], 3)
                self.__lcd.display_string(
                    "HIGH:{}{}".format(high_str, " OK" if ok else "")[:20], 4)

                log.info(
                    "Learn mode exit confirmation: low=%s high=%s samples=%d -> %s" % (
                        low_str, high_str, samples, "SUCCESS" if ok else "INCOMPLETE"))
        except Exception as e:
            log.error("Learn mode exit message error: %s" % str(e))

    def add_module(self, module):
        if isinstance(module, TBDeviceMQTTClient):
            self.__server = module
        elif isinstance(module, Battery):
            self.__battery = module
        elif isinstance(module, History):
            self.__history = module
        elif isinstance(module, GNSSBase):
            self.__gnss = module
        elif isinstance(module, CellLocator):
            self.__cell = module
        elif isinstance(module, WiFiLocator):
            self.__wifi = module
        elif isinstance(module, CoordinateSystemConvert):
            self.__csc = module
        elif isinstance(module, NetManager):
            self.__net_manager = module
        elif isinstance(module, Settings):
            self.__settings = module
        elif isinstance(module, LCD_CONTROL):
            self.__lcd = module
        elif isinstance(module, Modbus):
            self.__modbus = module
        elif isinstance(module, UART):
            self.__serial = module
        else:
            return False
        return True

    def running(self):
        self.__business_start()

        # Boot-once: establishes reboot count and downtime-since-last-seen early.
        self.__load_board_health()

        # Load valve calibration BEFORE the serial link starts.
        self.load_min_max()
        self.__boot_settle_time = utime.time()

        if self.__serial:
            self.__serial_start()
            log.debug("Serial communication started")
            # Push the just-loaded calibration to MSPM0 as early as possible.
            self.send_min_max_on_boot()

        self.__load_flow_base()

        global VALVE_STATUS
        VALVE_STATUS = self.previous_valve_status
        log.debug("Initialized VALVE_STATUS to %d%%" % VALVE_STATUS)

        global IMEI, IMSI
        try:
            IMEI = modem.getDevImei()
            log.info("Device IMEI: %s" % IMEI)
        except Exception as e:
            log.error("Failed to get IMEI: %s" % str(e))
            IMEI = "Unknown"

        try:
            IMSI = sim.getImsi()
            log.info("SIM IMSI: %s" % IMSI)
        except Exception as e:
            log.error("Failed to get IMSI: %s" % str(e))
            IMSI = "Unknown"
            self.__raise_generic_alert(
                "sim_missing",
                "Network Issue! Check the SIM",
                "CRITICAL")

        if self.__settings:
            self.__sms_config = SMSConfigHandler(
                self.__settings,
                self.__sms_config_changed_callback,
                IMEI
            )
            self.__sms_config.set_flow_callback(self.__update_flow_counter)
            self.__sms_config.set_timer_callback(self.__apply_timer_config)
            if hasattr(self.__sms_config, "set_server2_callback"):
                self.__sms_config.set_server2_callback(self.__sms_server2_changed_callback, self.__server2_state_text)
            else:
                # Older sms_config.py without this method - degrade instead of aborting boot.
                log.warning("SMSConfigHandler has no set_server2_callback - update sms_config.py; Server 2 SMS control disabled")
            self.__cloud_time_sec, sensor_read_sec = self.__sms_config.load_timer_config()
            self.__modbus_interval_ms = sensor_read_sec * 1000

            server_cfg = self.__settings.read("server")
            host, port, username = self.__read_server_status_json()
            if host and port and username:
                server_cfg["host"] = host
                server_cfg["port"] = port
                server_cfg["username"] = username
            else:
                log.warning("No valid server configuration found")
            self.__server = TBDeviceMQTTClient(**server_cfg)
            self.__server.set_callback(self.server_callback)
            self.__sms_config.start()
            log.info("SMS configuration handler started")
        else:
            log.warning("Settings not available, SMS config handler not started")

        self.server_connect(None)
        self.__business_queue.put((0, "server2_apply"))
        self.__business_queue.put((0, "modbus_read"))
        self.loc_report(None)

        if self.__modbus:
            self.__modbus_timer.start(self.__modbus_interval_ms, 1, self.modbus_read_callback)
            log.debug("Modbus timer started")

        if self.__lcd:
            self.__display_timer.start(5000, 1, self.display_read_callback)
            log.debug("Display timer started")

        if self.__serial:
            self.__serial_watchdog_timer.start(15000, 1, self.__serial_watchdog_check)
            self.__serial_last_rx_time = utime.time()
            log.debug("Serial watchdog started")

        self.__mem_check_timer.start(30000, 1, self.__memory_check)
        self.__last_free_mem = gc.mem_free()
        log.info("Memory monitoring started (free: %d bytes)" % self.__last_free_mem)

        self.__business_watchdog_timer.start(30000, 1, self.__business_watchdog_check)
        log.debug("Business-thread watchdog started")

        if self.__net_manager:
            # One-shot - __net_health_check reschedules itself with fast/slow interval.
            self.__net_health_check_timer.start(self.__net_health_check_fast_interval_ms, 0, self.__queue_net_health_check)
            log.debug("SIM/network health monitoring started")

    def server_callback(self, topic, data):
        self.__business_queue.put((1, (topic, data)))

    def server2_callback(self, topic, data):
        self.__business_queue.put((2, (topic, data)))

    def net_callback(self, args):
        log.debug("net_callback args: %s" % str(args))
        if args[1] == 0:
            try:
                self.__server.disconnect()
            except:
                pass
            self.__server_reconn_timer.stop()
            self.__server_reconn_timer.start(30 * 1000, 0, self.server_connect)
            if self.__server2 is not None:
                try:
                    self.__server2.disconnect()
                except:
                    pass
                self.__server2_reconn_timer.stop()
                self.__server2_reconn_timer.start(30 * 1000, 0, self.server2_connect)
        else:
            self.__server_reconn_timer.stop()
            self.server_connect(None)
            if self.__server2 is not None:
                self.__server2_reconn_timer.stop()
                self.server2_connect(None)

    def loc_report(self, args):
        self.__business_queue.put((0, "loc_report"))

    def server_connect(self, args):
        if self.__server_conn_tag == 0:
            self.__server_conn_tag = 1
            self.__business_queue.put((0, "server_connect"))

    def server2_connect(self, args):
        if self.__server2_conn_tag == 0:
            self.__server2_conn_tag = 1
            self.__business_queue.put((0, "server2_connect"))

    def gpio_read_callback(self, args):
        if self.__valve_control_in_progress:
            log.debug("Relay disable skipped - valve control in progress")
            return
        self.__business_queue.put((0, "modbus_read"))
        rel_value     = 0
        current_bytes = rel_value.to_bytes(8, 'little')
        packet_cur    = CANPacket(interface_type=0x01, can_cmd=0xAA02,
                                  data=list(current_bytes), seq_id=1234, crc_16=1234)
        self.__business_queue.put((0, "serial_send", packet_cur))
        self.__gpio_timer.stop()

    def modbus_read_callback(self, args):
        if self.__valve_control_in_progress:
            elapsed = utime.time() - self.__valve_control_start_time
            if elapsed > 90:
                log.error("SAFETY: Valve control stuck for %ds, forcing resume" % int(elapsed))
                self.__valve_control_in_progress = False
            else:
                return
        rel_value     = 1
        current_bytes = rel_value.to_bytes(8, 'little')
        packet_cur    = CANPacket(interface_type=0x01, can_cmd=0xAA02,
                                  data=list(current_bytes), seq_id=1234, crc_16=1234)
        self.__business_queue.put((0, "serial_send", packet_cur))
        self.__gpio_timer.start(60000, 1, self.gpio_read_callback)

    def __suspend_display_timer(self):
        try:
            self.__display_resume_timer.stop()
            self.__display_suspended = True
            self.__display_resume_timer.start(10000, 0, self.__resume_display_timer)
        except Exception as e:
            log.error("Error suspending display timer: %s" % str(e))

    def __resume_display_timer(self, args):
        try:
            self.__display_suspended = False
        except Exception as e:
            log.error("Error resuming display timer: %s" % str(e))

    def display_read_callback(self, args):
        try:
            global LEARN_MODE
            # Leak alert overrides everything, including the display-suspension window.
            if self.__leak_alert_active:
                if self.__lcd:
                    with self.__display_lock:
                        self.__display_leak_alert()
                return
            # Generic alerts take next priority, same reasoning.
            _generic_alert = self.__highest_severity_generic_alert()
            if _generic_alert:
                if self.__lcd:
                    with self.__display_lock:
                        self.__display_generic_alert(_generic_alert[0], _generic_alert[1])
                return
            if self.__display_suspended:
                return
            if self.__lcd:
                with self.__display_lock:
                    if LEARN_MODE == 1:
                        self.__display_page_learn()
                    elif self.__valve_control_in_progress:
                        self.__display_page_4()
                    else:
                        if   self.page == 1: self.__display_page_1()
                        elif self.page == 2: self.__display_page_2()
                        elif self.page == 3: self.__display_page_3()
                        elif self.page == 4: self.__display_page_4()
                        elif self.page == 5: self.__display_page_5()
                        self.page = self.page + 1 if self.page < 5 else 1
        except Exception as e:
            log.error("Display rotation error: %s" % str(e))

def run():
    try:
        lcd = LCD_CONTROL()
        lcd.init()
        utime.sleep_ms(200)
        lcd.display_string("WATER QUALITY", 1)
        lcd.display_string("MONITORING SYSTEM", 2)
        lcd.display_string("Initializing...", 3)
        lcd.display_string("", 4)
    except Exception as e:
        log.error("Failed to initialize LCD: %s" % str(e))
        lcd = None

    settings     = Settings()
    battery      = Battery()
    history      = History()
    power_manage = PowerManage()
    power_manage.autosleep(0)

    loc_cfg = settings.read("loc")
    try:
        log.info("Initializing GNSS...")
        gnss = GNSS(**loc_cfg["gps_cfg"])
        gnss.set_trans(0)
        gnss_start_result = gnss.start()
        if not gnss_start_result:
            log.error("GNSS thread failed to start!")
            gnss = None
        else:
            utime.sleep_ms(2000)
            test_data = gnss.read()
            log.info("GNSS read: state=%s satellites=%s" % (
                test_data.get("state", "N/A"), test_data.get("satellites", "N/A")))
    except Exception as e:
        log.error("Failed to initialize GNSS: %s" % str(e))
        import sys
        sys.print_exception(e)
        gnss = None

    net_manager = NetManager()
    _thread.stack_size(0x1000)
    _thread.start_new_thread(net_manager.net_connect, ())

    cell = CellLocator(**loc_cfg["cell_cfg"])
    wifi = WiFiLocator(**loc_cfg["wifi_cfg"])
    cyc  = CoordinateSystemConvert()

    try:
        serial = UART(UART.UART2, 115200, 8, 0, 1, 0)
        log.debug("Serial UART2 initialized")
    except Exception as e:
        log.error("Failed to initialize Serial UART2: %s" % str(e))
        serial = None

    try:
        modbus = Modbus(UART.UART1, 9600, Pin.GPIO7)
        log.debug("Modbus initialized")
    except Exception as e:
        log.error("Failed to initialize Modbus: %s" % str(e))
        modbus = None

    tracker = Tracker()
    tracker.add_module(settings)
    tracker.add_module(battery)
    tracker.add_module(history)
    tracker.add_module(net_manager)
    tracker.add_module(gnss)
    tracker.add_module(cell)
    tracker.add_module(wifi)
    tracker.add_module(cyc)
    tracker.add_module(lcd)
    tracker.add_module(modbus)
    tracker.add_module(serial)

    net_manager.set_callback(tracker.net_callback)
    tracker.running()